"""
Sprint 6.03: Joint MSE-Gap Optimization for IVF Codebooks
==========================================================
Transfers the exact methodology that worked for kissing numbers to vector quantization.

Key insight: Sequential approaches (6.01, 6.02) failed because they optimize conflicting
objectives sequentially. Joint optimization combines MSE (covering) and gap (packing)
into a single objective.

Loss = MSE + λ * gap_penalty

The kissing number optimizer succeeded because of:
1. Continuous gradient descent (not alternating steps)
2. Annealed Adam with tangent projection
3. Soft-min for differentiable gap

All of these transfer directly here.

Author: R.J. Mathews
Date: 2026-01-30
Prerequisites: Sprint 6.01 (baseline), Sprint 6.02 (rotation failed)
"""

import numpy as np
import json
import csv
import time
from dataclasses import dataclass, asdict
from typing import Dict, List, Tuple, Any, Optional
from pathlib import Path

# Import from previous sprints
from sprint520_bookend_controls import (
    project_all, project_grad_tangent, AdamState
)
from sprint601_ivf_benchmark import (
    generate_normalized_data, init_random, init_kmeans_pp, init_spherical_code,
    run_kmeans, compute_recall_at_k, ExperimentConfig
)


# =============================================================================
# 1. Core Joint Loss Function
# =============================================================================

def compute_min_separation(C: np.ndarray) -> float:
    """Compute minimum pairwise distance between centroids."""
    dists = np.linalg.norm(C[:, None, :] - C[None, :, :], axis=2)
    np.fill_diagonal(dists, np.inf)
    return float(np.min(dists))


def soft_mse_and_grad(C: np.ndarray, X: np.ndarray, tau: float) -> Tuple[float, np.ndarray]:
    """
    Compute soft MSE and gradient using soft assignments.

    Uses temperature-controlled softmax assignments instead of hard argmin.

    Args:
        C: (N, d) centroids
        X: (n, d) data points
        tau: temperature (lower = harder assignments)

    Returns:
        mse: scalar MSE value
        grad: (N, d) gradient w.r.t. C
    """
    N, d = C.shape
    n = len(X)

    # Compute squared distances using dot products for efficiency
    # ||x - c||^2 = ||x||^2 + ||c||^2 - 2*x.c = 2(1 - x.c) for unit vectors
    dots = X @ C.T  # (n, N)
    dots = np.clip(dots, -1.0, 1.0)
    dists_sq = 2.0 * (1.0 - dots)  # (n, N)

    # Soft assignments (softmax over centroids)
    logits = -dists_sq / tau
    logits = logits - logits.max(axis=1, keepdims=True)  # Numerical stability
    weights = np.exp(logits)
    weights = weights / (weights.sum(axis=1, keepdims=True) + 1e-12)  # (n, N)

    # MSE = mean over data of weighted squared distances
    mse = float(np.mean(np.sum(weights * dists_sq, axis=1)))

    # Gradient of MSE w.r.t. C
    # For each centroid j: grad_j = (2/n) * sum_i w_ij * (c_j - x_i)
    # Using matrix ops: grad = (2/n) * (weights.T @ (-X) + diag(weights.sum(0)) @ C)
    grad = np.zeros_like(C)
    weights_sum = weights.sum(axis=0)  # (N,)
    for j in range(N):
        # grad[j] = (2/n) * sum_i w_ij * (C[j] - X[i])
        # = (2/n) * (sum_i w_ij * C[j] - sum_i w_ij * X[i])
        # = (2/n) * (weights_sum[j] * C[j] - weights[:, j] @ X)
        grad[j] = (2.0 / n) * (weights_sum[j] * C[j] - weights[:, j] @ X)

    return mse, grad


def soft_gap_and_grad(C: np.ndarray, tau: float) -> Tuple[float, np.ndarray]:
    """
    Compute soft minimum separation (gap) and gradient using logsumexp.

    This is the same soft-min from sprint520 that worked for kissing numbers.

    Args:
        C: (N, d) centroids
        tau: temperature (lower = sharper)

    Returns:
        soft_min: smooth approximation of min pairwise distance
        grad: (N, d) gradient w.r.t. C (to INCREASE soft_min)
    """
    N, d = C.shape

    # Pairwise distances
    diffs = C[:, None, :] - C[None, :, :]  # (N, N, d)
    dists = np.linalg.norm(diffs, axis=2)  # (N, N)
    np.fill_diagonal(dists, np.inf)

    # Soft-min via logsumexp: soft_min ≈ min_ij d_ij
    neg_dists = -dists / tau
    np.fill_diagonal(neg_dists, -np.inf)

    max_val = np.max(neg_dists)
    if np.isinf(max_val):
        return 0.0, np.zeros_like(C)

    exp_vals = np.exp(neg_dists - max_val)
    sum_exp = np.sum(exp_vals)
    if sum_exp < 1e-300:
        return 0.0, np.zeros_like(C)

    soft_min = -tau * (np.log(sum_exp) + max_val)

    # Gradient of soft_min w.r.t. C
    # d(soft_min)/d(d_ij) = exp(-d_ij/tau) / sum_k exp(-d_k/tau)
    # d(d_ij)/d(C_i) = (C_i - C_j) / d_ij
    weights = exp_vals / sum_exp
    np.fill_diagonal(weights, 0.0)

    denom = np.maximum(dists, 1e-12)
    coeff = weights / denom  # (N, N)

    # Gradient: for each point i, sum contributions from all pairs involving i
    grad = np.zeros_like(C)
    for i in range(N):
        for j in range(N):
            if i != j:
                direction = diffs[i, j] / denom[i, j]  # Unit vector i -> j
                # d(soft_min)/d(C_i) includes +coeff[i,j]*direction (from pair (i,j))
                grad[i] += coeff[i, j] * direction

    return float(soft_min), grad


def joint_loss_and_grad(C: np.ndarray, X: np.ndarray,
                        lambda_gap: float, theta_target: float,
                        tau_mse: float, tau_gap: float) -> Tuple[float, np.ndarray, Dict]:
    """
    Joint MSE + gap penalty loss with gradients.

    L = MSE + lambda * max(0, theta_target - gap)

    Args:
        C: (N, d) centroids on unit sphere
        X: (n, d) data on unit sphere
        lambda_gap: weight for gap penalty
        theta_target: target minimum separation
        tau_mse: temperature for soft MSE
        tau_gap: temperature for soft gap

    Returns:
        loss: scalar total loss
        grad: (N, d) gradient w.r.t. C
        metrics: dict with individual components
    """
    # MSE term
    mse, grad_mse = soft_mse_and_grad(C, X, tau_mse)

    # Gap term
    gap, grad_gap = soft_gap_and_grad(C, tau_gap)

    # Gap penalty: penalize if gap < theta_target
    gap_violation = theta_target - gap
    if gap_violation > 0:
        gap_penalty = gap_violation
        # Gradient of penalty = -grad_gap (penalty decreases when gap increases)
        grad_penalty = -grad_gap
    else:
        gap_penalty = 0.0
        grad_penalty = np.zeros_like(C)

    # Combined loss and gradient
    loss = mse + lambda_gap * gap_penalty
    grad = grad_mse + lambda_gap * grad_penalty

    metrics = {
        'mse': mse,
        'gap': gap,
        'gap_penalty': gap_penalty,
        'lambda': lambda_gap
    }

    return loss, grad, metrics


# =============================================================================
# 2. Joint Optimizer
# =============================================================================

def optimize_joint(X: np.ndarray, N: int,
                   init_method: str = 'spherical',
                   lambda_init: float = 1.0,
                   lambda_final: float = 0.01,
                   theta_target: Optional[float] = None,
                   n_iters: int = 5000,
                   lr: float = 0.01,
                   batch_size: int = 2000,
                   seed: int = 42,
                   verbose: bool = True) -> Dict[str, Any]:
    """
    Joint optimization of MSE + gap penalty.

    Uses annealed Adam with tangent projection - same methodology as kissing numbers.

    Args:
        X: (n, d) data on unit sphere
        N: number of centroids
        init_method: 'spherical', 'random', or 'kmeans_pp'
        lambda_init: initial gap weight (high = focus on separation)
        lambda_final: final gap weight (low = focus on MSE)
        theta_target: target separation (None = use 80% of spherical code gap)
        n_iters: optimization iterations
        lr: learning rate
        batch_size: mini-batch size for MSE computation
        seed: random seed
        verbose: print progress

    Returns:
        dict with 'centroids', 'history', 'final_mse', 'final_gap'
    """
    n, d = X.shape
    rng = np.random.default_rng(seed)

    # Initialize centroids
    if init_method == 'spherical':
        C, init_opt_gap = init_spherical_code(N, d, seed, restarts=3, iters=2000)
        if verbose:
            print(f"  Spherical init gap: {compute_min_separation(C):.4f}")
    elif init_method == 'random':
        C = init_random(N, d, seed)
    elif init_method == 'kmeans_pp':
        C = init_kmeans_pp(X, N, seed)
    else:
        raise ValueError(f"Unknown init method: {init_method}")

    C = C.astype(np.float64)  # Use float64 for optimization

    # Set theta_target based on k-means++ achievable gap (NOT spherical code gap!)
    # Bug fix: spherical gap doesn't scale with N, but achievable gap does
    if theta_target is None:
        # Quick k-means++ to find achievable gap
        kmpp_ref = init_kmeans_pp(X, N, seed + 1000)
        kmpp_result = run_kmeans(X, kmpp_ref, max_iters=50)
        achievable_gap = compute_min_separation(kmpp_result['centroids'])
        theta_target = 0.95 * achievable_gap  # Target 95% of k-means++ gap
        if verbose:
            print(f"  k-means++ achievable gap: {achievable_gap:.4f}, Target: {theta_target:.4f}")

    # Adam state
    adam = AdamState(C.shape)

    # Temperature schedules
    tau_mse_init = 0.5
    tau_mse_min = 0.05
    tau_gap_init = 0.1
    tau_gap_min = 0.01
    tau_decay = 0.9995

    # History
    history = {'mse': [], 'gap': [], 'lambda': [], 'loss': []}

    for t in range(n_iters):
        # Anneal lambda: exponential decay
        progress = t / n_iters
        lambda_t = lambda_init * (lambda_final / lambda_init) ** progress

        # Anneal temperatures
        tau_mse = max(tau_mse_min, tau_mse_init * (tau_decay ** t))
        tau_gap = max(tau_gap_min, tau_gap_init * (tau_decay ** t))

        # Mini-batch for MSE (full data for gap since it's O(N^2))
        batch_idx = rng.choice(n, min(batch_size, n), replace=False)
        X_batch = X[batch_idx]

        # Compute loss and gradient
        loss, grad, metrics = joint_loss_and_grad(
            C, X_batch, lambda_t, theta_target, tau_mse, tau_gap
        )

        # Project gradient to tangent space (sphere constraint)
        grad = project_grad_tangent(C, grad)

        # Clip gradient for stability
        grad_norm = np.linalg.norm(grad)
        if grad_norm > 1.0:
            grad = grad / grad_norm

        # Adam step
        step = adam.step(grad, lr)
        C = C - step

        # Project back to unit sphere
        C = project_all(C, 1.0)

        # Log
        history['mse'].append(metrics['mse'])
        history['gap'].append(metrics['gap'])
        history['lambda'].append(lambda_t)
        history['loss'].append(loss)

        if verbose and t % 1000 == 0:
            print(f"    Iter {t}: MSE={metrics['mse']:.4f}, Gap={metrics['gap']:.4f}, "
                  f"lambda={lambda_t:.4f}, Penalty={metrics['gap_penalty']:.4f}")

    # Final metrics (hard assignment on full data)
    C = C.astype(np.float32)
    final_mse = compute_hard_mse(C, X)
    final_gap = compute_min_separation(C)

    if verbose:
        print(f"  Final: MSE={final_mse:.4f}, Gap={final_gap:.4f}")

    return {
        'centroids': C,
        'history': history,
        'final_mse': final_mse,
        'final_gap': final_gap,
        'theta_target': theta_target,
        'init_method': init_method
    }


def compute_hard_mse(C: np.ndarray, X: np.ndarray) -> float:
    """Compute MSE with hard (argmin) assignments."""
    # Use dot product for efficiency
    dots = X @ C.T
    dots = np.clip(dots, -1.0, 1.0)
    dists_sq = 2.0 * (1.0 - dots)
    min_dists_sq = np.min(dists_sq, axis=1)
    return float(np.mean(min_dists_sq))


# =============================================================================
# 3. Experiment Runner
# =============================================================================

@dataclass
class JointExperimentConfig:
    """Configuration for joint optimization experiment."""
    n_centroids: int
    dim: int
    n_samples: int
    n_clusters: int
    cluster_std: float
    seed: int
    n_queries: int = 1000
    k: int = 10
    joint_iters: int = 5000
    joint_lr: float = 0.01
    lambda_init: float = 1.0
    lambda_final: float = 0.01
    batch_size: int = 2000


def run_single_experiment(config: JointExperimentConfig) -> Dict[str, Any]:
    """
    Run experiment comparing k-means, k-means++, and joint optimization.
    """
    print(f"  Generating data (n={config.n_samples}, dim={config.dim})...")

    # Generate data
    data = generate_normalized_data(
        n_samples=config.n_samples,
        dim=config.dim,
        n_clusters=config.n_clusters,
        cluster_std=config.cluster_std,
        seed=config.seed
    )

    # Generate queries
    queries = generate_normalized_data(
        n_samples=config.n_queries,
        dim=config.dim,
        n_clusters=config.n_clusters,
        cluster_std=config.cluster_std,
        seed=config.seed + 10000
    )

    results = {
        'config': asdict(config),
        'methods': {}
    }

    # Helper to evaluate
    def evaluate(name: str, centroids: np.ndarray, init_time: float,
                 extra: dict = None):
        recall = compute_recall_at_k(data, centroids, queries, k=config.k)
        result = {
            'init_time_sec': init_time,
            'final_mse': compute_hard_mse(centroids, data),
            'final_gap': compute_min_separation(centroids),
            'recall_at_k': recall
        }
        if extra:
            result.update(extra)
        results['methods'][name] = result
        print(f"    {name}: MSE={result['final_mse']:.4f}, "
              f"Gap={result['final_gap']:.4f}, Recall@10={recall.get(10, 0):.3f}")

    # Method 1: k-means (random init)
    print("    Running k-means (random init)...")
    t0 = time.time()
    init_rand = init_random(config.n_centroids, config.dim, config.seed)
    kmeans_rand = run_kmeans(data, init_rand, max_iters=100)
    t1 = time.time()
    evaluate('kmeans_random', kmeans_rand['centroids'], t1 - t0,
             {'iterations': kmeans_rand['iterations']})

    # Method 2: k-means++
    print("    Running k-means++...")
    t0 = time.time()
    init_kpp = init_kmeans_pp(data, config.n_centroids, config.seed)
    kmeans_kpp = run_kmeans(data, init_kpp, max_iters=100)
    t1 = time.time()
    evaluate('kmeans_pp', kmeans_kpp['centroids'], t1 - t0,
             {'iterations': kmeans_kpp['iterations']})

    # Method 3: Joint optimization (random init)
    print("    Running Joint (random init)...")
    t0 = time.time()
    joint_rand = optimize_joint(
        data, config.n_centroids,
        init_method='random',
        lambda_init=config.lambda_init,
        lambda_final=config.lambda_final,
        n_iters=config.joint_iters,
        lr=config.joint_lr,
        batch_size=config.batch_size,
        seed=config.seed,
        verbose=False
    )
    t1 = time.time()
    evaluate('joint_random', joint_rand['centroids'], t1 - t0,
             {'theta_target': joint_rand['theta_target']})

    # Method 4: Joint optimization (spherical init)
    print("    Running Joint (spherical init)...")
    t0 = time.time()
    joint_spherical = optimize_joint(
        data, config.n_centroids,
        init_method='spherical',
        lambda_init=config.lambda_init,
        lambda_final=config.lambda_final,
        n_iters=config.joint_iters,
        lr=config.joint_lr,
        batch_size=config.batch_size,
        seed=config.seed,
        verbose=False
    )
    t1 = time.time()
    evaluate('joint_spherical', joint_spherical['centroids'], t1 - t0,
             {'theta_target': joint_spherical['theta_target']})

    return results


# =============================================================================
# 4. Benchmark Suite
# =============================================================================

def run_benchmark_suite(out_dir: Path, n_samples: int = 50000, dim: int = 128,
                        n_clusters: int = 100, cluster_std: float = 0.3,
                        seeds: List[int] = [601, 602, 603],
                        n_centroids_list: List[int] = [64, 256],
                        joint_iters: int = 5000) -> Dict[str, Any]:
    """Run full benchmark."""
    out_dir.mkdir(parents=True, exist_ok=True)

    all_results = {
        'config': {
            'n_samples': n_samples,
            'dim': dim,
            'n_clusters': n_clusters,
            'cluster_std': cluster_std,
            'seeds': seeds,
            'n_centroids_list': n_centroids_list,
            'joint_iters': joint_iters
        },
        'timestamp': time.strftime("%Y-%m-%d %H:%M:%S"),
        'experiments': []
    }

    total_runs = len(n_centroids_list) * len(seeds)
    run_count = 0

    for N in n_centroids_list:
        print(f"\n{'='*60}")
        print(f"N_centroids = {N}")
        print(f"{'='*60}")

        for seed in seeds:
            run_count += 1
            print(f"\n[Run {run_count}/{total_runs}] N={N}, seed={seed}")

            config = JointExperimentConfig(
                n_centroids=N,
                dim=dim,
                n_samples=n_samples,
                n_clusters=n_clusters,
                cluster_std=cluster_std,
                seed=seed,
                joint_iters=joint_iters
            )

            result = run_single_experiment(config)
            all_results['experiments'].append(result)

            # Save individual result
            result_path = out_dir / f"N{N}_seed{seed}.json"
            with open(result_path, 'w') as f:
                json.dump(result, f, indent=2)

    return all_results


# =============================================================================
# 5. Analysis
# =============================================================================

def aggregate_results(all_results: Dict[str, Any]) -> Dict[str, Any]:
    """Aggregate results across seeds."""
    by_n = {}
    for exp in all_results['experiments']:
        N = exp['config']['n_centroids']
        if N not in by_n:
            by_n[N] = []
        by_n[N].append(exp)

    summary = {
        'config': all_results['config'],
        'timestamp': all_results['timestamp'],
        'by_n_centroids': {}
    }

    methods = ['kmeans_random', 'kmeans_pp', 'joint_random', 'joint_spherical']

    for N, experiments in sorted(by_n.items()):
        n_trials = len(experiments)
        methods_summary = {}

        for method in methods:
            if method not in experiments[0]['methods']:
                continue

            mse = [e['methods'][method]['final_mse'] for e in experiments]
            gap = [e['methods'][method]['final_gap'] for e in experiments]
            recall_10 = [e['methods'][method]['recall_at_k'].get(10, 0) for e in experiments]
            init_time = [e['methods'][method]['init_time_sec'] for e in experiments]

            methods_summary[method] = {
                'mse_mean': float(np.mean(mse)),
                'mse_std': float(np.std(mse)),
                'gap_mean': float(np.mean(gap)),
                'gap_std': float(np.std(gap)),
                'recall_10_mean': float(np.mean(recall_10)),
                'recall_10_std': float(np.std(recall_10)),
                'init_time_mean': float(np.mean(init_time)),
            }

        # Compute comparisons (joint vs k-means++)
        kpp = methods_summary['kmeans_pp']

        comparisons = {}
        for joint_method in ['joint_random', 'joint_spherical']:
            if joint_method not in methods_summary:
                continue
            joint = methods_summary[joint_method]

            gap_improvement = (joint['gap_mean'] - kpp['gap_mean']) / kpp['gap_mean'] * 100
            mse_diff = (joint['mse_mean'] - kpp['mse_mean']) / kpp['mse_mean'] * 100
            recall_diff = joint['recall_10_mean'] - kpp['recall_10_mean']

            comparisons[joint_method] = {
                'gap_improvement_vs_kpp_pct': gap_improvement,
                'mse_diff_vs_kpp_pct': mse_diff,
                'recall_diff_vs_kpp': recall_diff
            }

        summary['by_n_centroids'][N] = {
            'n_trials': n_trials,
            'methods': methods_summary,
            'comparisons': comparisons
        }

    return summary


def check_success_criteria(summary: Dict[str, Any]) -> Dict[str, Any]:
    """
    Check Sprint 6.03 success criteria:
    1. Gap >= 20% better than k-means++
    2. MSE within 5% of k-means++
    3. Recall within 2% of k-means++
    """
    criteria = {}

    for N, data in summary['by_n_centroids'].items():
        criteria[N] = {}

        for method, comp in data['comparisons'].items():
            # Criterion 1: Gap >= 20% better
            gap_improvement = comp['gap_improvement_vs_kpp_pct']
            c1_pass = gap_improvement >= 20.0

            # Criterion 2: MSE within 5%
            mse_diff = comp['mse_diff_vs_kpp_pct']
            c2_pass = mse_diff <= 5.0

            # Criterion 3: Recall within 2%
            recall_diff = comp['recall_diff_vs_kpp']
            c3_pass = recall_diff >= -0.02

            criteria[N][method] = {
                'criterion_1_gap': {
                    'target': 'Gap >= 20% better than k-means++',
                    'actual': f'{gap_improvement:+.1f}%',
                    'pass': c1_pass
                },
                'criterion_2_mse': {
                    'target': 'MSE within 5% of k-means++',
                    'actual': f'{mse_diff:+.1f}%',
                    'pass': c2_pass
                },
                'criterion_3_recall': {
                    'target': 'Recall within 2% of k-means++',
                    'actual': f'{recall_diff:+.3f}',
                    'pass': c3_pass
                },
                'all_pass': c1_pass and c2_pass and c3_pass
            }

    return criteria


def generate_report(summary: Dict[str, Any], criteria: Dict[str, Any], report_path: Path):
    """Generate comprehensive markdown report."""
    lines = [
        "# Sprint 6.03: Joint MSE-Gap Optimization",
        "",
        f"**Generated:** {summary['timestamp']}",
        "",
        "## Executive Summary",
        "",
        "This experiment tests **joint optimization** of MSE (quantization error) and gap (separation),",
        "using the same methodology that succeeded for kissing number certification.",
        "",
        "### Key Insight",
        "",
        "Sequential approaches (6.01, 6.02) failed because they optimize conflicting objectives one after another.",
        "Joint optimization combines them into a single loss: L = MSE + λ·gap_penalty",
        "",
        "---",
        "",
        "## Configuration",
        "",
        f"- **Data points:** {summary['config']['n_samples']:,}",
        f"- **Dimension:** {summary['config']['dim']}",
        f"- **Codebook sizes:** {summary['config']['n_centroids_list']}",
        f"- **Seeds:** {summary['config']['seeds']}",
        f"- **Joint iterations:** {summary['config']['joint_iters']}",
        "",
        "---",
        "",
        "## Results",
        "",
    ]

    # Results table
    for N in sorted(summary['by_n_centroids'].keys()):
        data = summary['by_n_centroids'][N]
        lines.extend([
            f"### N = {N} Centroids",
            "",
            "| Method | MSE | Gap | Recall@10 | Time |",
            "|--------|-----|-----|-----------|------|",
        ])

        method_names = {
            'kmeans_random': 'k-means (random)',
            'kmeans_pp': 'k-means++',
            'joint_random': 'Joint (random)',
            'joint_spherical': 'Joint (spherical)'
        }

        for method in ['kmeans_random', 'kmeans_pp', 'joint_random', 'joint_spherical']:
            if method not in data['methods']:
                continue
            m = data['methods'][method]
            lines.append(
                f"| {method_names[method]} | "
                f"{m['mse_mean']:.4f} +/- {m['mse_std']:.4f} | "
                f"{m['gap_mean']:.4f} +/- {m['gap_std']:.4f} | "
                f"{m['recall_10_mean']:.3f} +/- {m['recall_10_std']:.3f} | "
                f"{m['init_time_mean']:.1f}s |"
            )
        lines.append("")

    # Comparison table
    lines.extend([
        "---",
        "",
        "## Joint vs k-means++ Comparison",
        "",
        "| N | Method | Gap Improvement | MSE Diff | Recall Diff |",
        "|---|--------|-----------------|----------|-------------|",
    ])

    for N in sorted(summary['by_n_centroids'].keys()):
        for method, comp in summary['by_n_centroids'][N]['comparisons'].items():
            method_short = method.replace('joint_', '')
            lines.append(
                f"| {N} | {method_short} | "
                f"{comp['gap_improvement_vs_kpp_pct']:+.1f}% | "
                f"{comp['mse_diff_vs_kpp_pct']:+.1f}% | "
                f"{comp['recall_diff_vs_kpp']:+.3f} |"
            )

    lines.extend(["", "---", ""])

    # Success criteria
    lines.extend([
        "## Success Criteria Evaluation",
        "",
        "| N | Method | Gap (≥20%) | MSE (≤5%) | Recall (≥-2%) | All Pass |",
        "|---|--------|------------|-----------|---------------|----------|",
    ])

    any_pass = False
    for N in sorted(criteria.keys()):
        for method, c in criteria[N].items():
            method_short = method.replace('joint_', '')
            c1 = "PASS" if c['criterion_1_gap']['pass'] else "FAIL"
            c2 = "PASS" if c['criterion_2_mse']['pass'] else "FAIL"
            c3 = "PASS" if c['criterion_3_recall']['pass'] else "FAIL"
            all_p = "**YES**" if c['all_pass'] else "no"
            if c['all_pass']:
                any_pass = True
            lines.append(f"| {N} | {method_short} | {c1} | {c2} | {c3} | {all_p} |")

    lines.extend(["", ""])

    # Verdict
    if any_pass:
        verdict = "**HYPOTHESIS SUPPORTED**: Joint optimization achieves better gap with competitive MSE and recall."
    else:
        verdict = "**HYPOTHESIS NOT SUPPORTED**: Joint optimization does not meet all success criteria."

    lines.extend([
        "## Verdict",
        "",
        verdict,
        "",
        "---",
        "",
        "## Interpretation",
        "",
    ])

    # Check if gap improved
    gap_improved = False
    for N in summary['by_n_centroids']:
        for method, comp in summary['by_n_centroids'][N]['comparisons'].items():
            if comp['gap_improvement_vs_kpp_pct'] > 0:
                gap_improved = True

    if gap_improved:
        lines.extend([
            "### Gap Regularization Works",
            "",
            "Joint optimization achieves better separation than pure k-means.",
            "This validates the core hypothesis: gap penalty prevents codebook collapse.",
            "",
        ])
    else:
        lines.extend([
            "### Gap Regularization Does Not Help",
            "",
            "Joint optimization does not achieve better separation than k-means.",
            "The packing objective may interfere with the clustering objective.",
            "",
        ])

    lines.extend([
        "---",
        "",
        "*Report generated by sprint603_joint_optimization.py*",
    ])

    with open(report_path, 'w') as f:
        f.write('\n'.join(lines))


def results_to_csv(all_results: Dict[str, Any], csv_path: Path):
    """Export results to CSV."""
    rows = []

    for exp in all_results['experiments']:
        N = exp['config']['n_centroids']
        seed = exp['config']['seed']

        for method, m in exp['methods'].items():
            rows.append({
                'n_centroids': N,
                'seed': seed,
                'method': method,
                'init_time_sec': m['init_time_sec'],
                'final_mse': m['final_mse'],
                'final_gap': m['final_gap'],
                'recall_nprobe_10': m['recall_at_k'].get(10, None)
            })

    with open(csv_path, 'w', newline='') as f:
        if rows:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)


# =============================================================================
# 6. Main
# =============================================================================

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Sprint 6.03: Joint MSE-Gap Optimization"
    )
    parser.add_argument("--test", action="store_true",
                       help="Run small test")
    parser.add_argument("--n-samples", type=int, default=50000)
    parser.add_argument("--n-centroids", type=int, nargs="+", default=[64, 256])
    parser.add_argument("--seeds", type=int, nargs="+", default=[601, 602, 603])
    parser.add_argument("--joint-iters", type=int, default=5000)
    parser.add_argument("--out-dir", type=str, default="sprint603_joint")

    args = parser.parse_args()

    if args.test:
        # Small test
        print("="*60)
        print("Sprint 6.03: Small Test")
        print("="*60)

        config = JointExperimentConfig(
            n_centroids=64,
            dim=128,
            n_samples=10000,
            n_clusters=50,
            cluster_std=0.3,
            seed=601,
            joint_iters=2000
        )

        result = run_single_experiment(config)

        print("\n" + "="*60)
        print("Test Complete!")
        print("="*60)
        return

    # Full benchmark
    script_dir = Path(__file__).parent
    out_dir = script_dir / args.out_dir

    print("="*60)
    print("Sprint 6.03: Joint MSE-Gap Optimization")
    print("="*60)

    all_results = run_benchmark_suite(
        out_dir=out_dir / "results",
        n_samples=args.n_samples,
        seeds=args.seeds,
        n_centroids_list=args.n_centroids,
        joint_iters=args.joint_iters
    )

    # Save and analyze
    json_path = out_dir / "sprint603_results.json"
    with open(json_path, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved results: {json_path}")

    summary = aggregate_results(all_results)
    criteria = check_success_criteria(summary)

    summary_path = out_dir / "sprint603_summary.json"
    with open(summary_path, 'w') as f:
        json.dump({'summary': summary, 'criteria': criteria}, f, indent=2)

    csv_path = out_dir / "sprint603_results.csv"
    results_to_csv(all_results, csv_path)
    print(f"Saved CSV: {csv_path}")

    report_path = out_dir / "sprint603_report.md"
    generate_report(summary, criteria, report_path)
    print(f"Saved report: {report_path}")

    # Print summary
    print("\n" + "="*60)
    print("FINAL RESULTS")
    print("="*60)

    for N in sorted(criteria.keys()):
        print(f"\nN = {N}:")
        for method, c in criteria[N].items():
            method_short = method.replace('joint_', '')
            status = "ALL PASS" if c['all_pass'] else "FAIL"
            print(f"  {method_short}: {status}")
            print(f"    Gap: {c['criterion_1_gap']['actual']}")
            print(f"    MSE: {c['criterion_2_mse']['actual']}")
            print(f"    Recall: {c['criterion_3_recall']['actual']}")

    print("\n" + "="*60)


if __name__ == "__main__":
    main()
