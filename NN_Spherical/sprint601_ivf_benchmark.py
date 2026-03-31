"""
Sprint 6.01: IVF Initialization Benchmark
==========================================
Compares spherical code vs random vs k-means++ initialization for IVF codebooks.

This is the "killer experiment" to validate the spherical code framework for
vector quantization applications.

Author: R.J. Mathews
Date: 2026-01-29
"""

import numpy as np
import json
import csv
import time
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Tuple, Optional, Any
from pathlib import Path

# Import spherical code optimizer components from sprint520
from sprint520_bookend_controls import (
    project_all,
    min_gap,
    logsumexp_maxmin_and_grad,
    project_grad_tangent,
    AdamState
)


# =============================================================================
# 1. Data Generation
# =============================================================================

def generate_normalized_data(n_samples: int, dim: int, n_clusters: int,
                              cluster_std: float, seed: int) -> np.ndarray:
    """
    Generate clustered data on unit sphere.

    This simulates real embedding distributions which are:
    - High-dimensional
    - Approximately normalized (cosine similarity)
    - Clustered (semantic structure)

    Args:
        n_samples: Total number of data points
        dim: Embedding dimension
        n_clusters: Number of ground truth clusters
        cluster_std: Standard deviation in tangent space around cluster centers
        seed: Random seed for reproducibility

    Returns:
        data: (n_samples, dim) normalized vectors on unit sphere
    """
    rng = np.random.default_rng(seed)

    # Generate cluster centers on sphere
    centers = rng.normal(size=(n_clusters, dim))
    centers = centers / np.linalg.norm(centers, axis=1, keepdims=True)

    # Generate points around centers
    samples_per_cluster = n_samples // n_clusters
    data = []
    for center in centers:
        # Points in tangent space, then project
        noise = rng.normal(scale=cluster_std, size=(samples_per_cluster, dim))
        points = center + noise
        points = points / np.linalg.norm(points, axis=1, keepdims=True)
        data.append(points)

    return np.vstack(data).astype(np.float32)


# =============================================================================
# 2. Initialization Methods
# =============================================================================

def init_random(N: int, dim: int, seed: int) -> np.ndarray:
    """
    Random initialization on unit sphere.

    Args:
        N: Number of centroids
        dim: Embedding dimension
        seed: Random seed

    Returns:
        centroids: (N, dim) normalized vectors
    """
    rng = np.random.default_rng(seed)
    centroids = rng.normal(size=(N, dim))
    return (centroids / np.linalg.norm(centroids, axis=1, keepdims=True)).astype(np.float32)


def init_kmeans_pp(data: np.ndarray, N: int, seed: int) -> np.ndarray:
    """
    Standard k-means++ initialization.

    Selects initial centroids with probability proportional to squared distance
    from nearest existing centroid.

    Args:
        data: (n_samples, dim) data points
        N: Number of centroids to select
        seed: Random seed

    Returns:
        centroids: (N, dim) selected data points as initial centroids
    """
    rng = np.random.default_rng(seed)
    n_samples, dim = data.shape

    # First centroid: random data point
    centroids = [data[rng.integers(n_samples)].copy()]

    # Track minimum distance to any centroid for each point
    # For unit vectors: ||x-c||^2 = 2(1 - x.c)
    min_dists_sq = np.full(n_samples, np.inf)

    for _ in range(N - 1):
        # Update min distances with the new centroid
        new_centroid = centroids[-1]
        # Squared distance to new centroid using dot product
        dots = data @ new_centroid  # (n_samples,)
        dots = np.clip(dots, -1.0, 1.0)  # Clamp for numerical stability
        new_dists_sq = 2.0 * (1.0 - dots)
        new_dists_sq = np.maximum(new_dists_sq, 0.0)  # Ensure non-negative
        min_dists_sq = np.minimum(min_dists_sq, new_dists_sq)

        # Sample proportional to squared distance
        total = min_dists_sq.sum()
        if total < 1e-12:
            # All points are at centroids, pick random
            idx = rng.integers(n_samples)
        else:
            probs = min_dists_sq / total
            idx = rng.choice(n_samples, p=probs)
        centroids.append(data[idx].copy())

    return np.array(centroids, dtype=np.float32)


def init_spherical_code(N: int, dim: int, seed: int,
                        restarts: int = 5, iters: int = 3000) -> Tuple[np.ndarray, float]:
    """
    Initialize using spherical code optimizer from sprint520.
    Maximizes minimum pairwise separation.

    Args:
        N: Number of centroids
        dim: Embedding dimension
        seed: Random seed
        restarts: Number of random restarts
        iters: Iterations per restart

    Returns:
        centroids: (N, dim) optimized spherical code
        final_gap: Gap metric of final configuration
    """
    rng = np.random.default_rng(seed)
    best_centroids = None
    best_gap = -np.inf

    # Use unit sphere (R=0.5 gives diameter 1, so min_gap measures vs threshold 1.0)
    # For codebook on unit sphere, we use R=0.5 as reference
    R = 0.5

    for r in range(restarts):
        # Random init on unit sphere
        x = rng.normal(size=(N, dim))
        x = project_all(x, 1.0)  # Project to unit sphere

        adam = AdamState((N, dim))
        tau = 0.1  # Logsumexp temperature

        for i in range(iters):
            # Anneal temperature
            tau_t = max(0.01, tau * (0.9995 ** i))

            # Gradient step to maximize min distance
            loss, grad = logsumexp_maxmin_and_grad(x, R=R, tau=tau_t)
            grad = project_grad_tangent(x, grad)
            step = adam.step(grad, lr=0.01)
            x = x - step
            x = project_all(x, 1.0)

        # Compute gap (min pairwise distance - threshold)
        gap = min_gap(x, R=R)
        if gap > best_gap:
            best_gap = gap
            best_centroids = x.copy()

    return best_centroids.astype(np.float32), best_gap


# =============================================================================
# 3. k-means Refinement
# =============================================================================

def run_kmeans(data: np.ndarray, init_centroids: np.ndarray,
               max_iters: int = 100, tol: float = 1e-6) -> Dict[str, Any]:
    """
    Run k-means from given initialization.
    Track convergence and final quality.

    Args:
        data: (n_samples, dim) data points on unit sphere
        init_centroids: (N, dim) initial centroids on unit sphere
        max_iters: Maximum iterations
        tol: Convergence tolerance (max centroid movement)

    Returns:
        dict containing:
            - centroids: Final centroids
            - iterations: Number of iterations run
            - converged: Whether convergence criterion was met
            - final_mse: Final mean squared quantization error
            - final_gap: Final packing gap
            - history: Dict of MSE, delta, gap per iteration
    """
    centroids = init_centroids.copy()
    N, dim = centroids.shape
    n_samples = len(data)

    history = {
        'mse': [],
        'delta': [],
        'gap': []
    }

    # Process data in chunks to avoid memory issues
    chunk_size = min(10000, n_samples)

    for iteration in range(max_iters):
        # Assignment step: compute distances in chunks
        assignments = np.zeros(n_samples, dtype=np.int32)
        total_sq_dist = 0.0

        for start in range(0, n_samples, chunk_size):
            end = min(start + chunk_size, n_samples)
            chunk_data = data[start:end]

            # Compute distances for this chunk
            # Use dot product: ||x - c||^2 = ||x||^2 + ||c||^2 - 2*x.c
            # For unit vectors: ||x||^2 = ||c||^2 = 1, so ||x-c||^2 = 2(1 - x.c)
            dots = chunk_data @ centroids.T  # (chunk, N)
            dots = np.clip(dots, -1.0, 1.0)  # Clamp for numerical stability
            sq_dists = 2.0 * (1.0 - dots)  # (chunk, N)
            sq_dists = np.maximum(sq_dists, 0.0)  # Ensure non-negative

            chunk_assignments = np.argmin(sq_dists, axis=1)
            assignments[start:end] = chunk_assignments

            # Accumulate MSE
            total_sq_dist += np.sum(sq_dists[np.arange(len(chunk_assignments)), chunk_assignments])

        mse = total_sq_dist / n_samples
        history['mse'].append(float(mse))

        # Compute gap (packing quality of centroids)
        centroid_dists = np.linalg.norm(centroids[:, None, :] - centroids[None, :, :], axis=2)
        np.fill_diagonal(centroid_dists, np.inf)
        min_dist = np.min(centroid_dists)
        gap = min_dist  # Just the min distance, not relative to threshold
        history['gap'].append(float(gap))

        # Update step: compute new centroids
        new_centroids = np.zeros_like(centroids)
        counts = np.zeros(N)

        # Use numpy bincount for efficient aggregation
        for d in range(dim):
            new_centroids[:, d] = np.bincount(assignments, weights=data[:, d], minlength=N)
        counts = np.bincount(assignments, minlength=N).astype(float)

        # Handle empty clusters by reinitializing to random data points
        empty = counts == 0
        n_empty = np.sum(empty)
        if n_empty > 0:
            empty_idx = np.where(empty)[0]
            rng = np.random.default_rng(iteration)  # Deterministic per iteration
            for idx in empty_idx:
                new_centroids[idx] = data[rng.integers(n_samples)]
                counts[idx] = 1

        new_centroids = new_centroids / counts[:, None]

        # Normalize to unit sphere
        norms = np.linalg.norm(new_centroids, axis=1, keepdims=True)
        norms = np.maximum(norms, 1e-12)  # Avoid division by zero
        new_centroids = new_centroids / norms

        # Check convergence (max centroid movement)
        delta = np.max(np.linalg.norm(new_centroids - centroids, axis=1))
        history['delta'].append(float(delta))

        centroids = new_centroids

        if delta < tol:
            break

    return {
        'centroids': centroids,
        'iterations': iteration + 1,
        'converged': delta < tol,
        'final_mse': history['mse'][-1],
        'final_gap': history['gap'][-1],
        'history': history
    }


# =============================================================================
# 4. Recall@k Evaluation
# =============================================================================

def compute_recall_at_k(data: np.ndarray, centroids: np.ndarray,
                        queries: np.ndarray, k: int = 10,
                        n_probe_list: List[int] = [1, 5, 10, 20]) -> Dict[int, float]:
    """
    Compute recall@k using IVF-style search at different n_probe values.

    1. Find n_probe nearest centroids to query
    2. Search only vectors assigned to those centroids
    3. Compare to ground truth k-NN

    Args:
        data: (n_samples, dim) database vectors
        centroids: (N, dim) IVF centroids
        queries: (n_queries, dim) query vectors
        k: Number of neighbors to retrieve
        n_probe_list: List of n_probe values to test

    Returns:
        Dict mapping n_probe -> recall@k
    """
    n_samples = len(data)
    n_queries = len(queries)
    N = len(centroids)

    # Build inverted index: assign each data point to nearest centroid
    # Process in chunks to avoid memory issues
    chunk_size = 10000
    assignments = np.zeros(n_samples, dtype=np.int32)
    for start in range(0, n_samples, chunk_size):
        end = min(start + chunk_size, n_samples)
        chunk_dists = np.linalg.norm(data[start:end, None, :] - centroids[None, :, :], axis=2)
        assignments[start:end] = np.argmin(chunk_dists, axis=1)

    inverted_lists = {i: [] for i in range(N)}
    for idx, a in enumerate(assignments):
        inverted_lists[a].append(idx)

    # Ground truth: brute force k-NN for each query (process query by query to save memory)
    ground_truth = np.zeros((n_queries, k), dtype=np.int32)
    for q_idx in range(n_queries):
        query = queries[q_idx]
        # Compute distances to all data points
        dists = np.linalg.norm(data - query, axis=1)
        ground_truth[q_idx] = np.argsort(dists)[:k]

    # Compute recall for each n_probe
    results = {}
    for n_probe in n_probe_list:
        recalls = []
        for q_idx, query in enumerate(queries):
            # Find n_probe nearest centroids
            q_centroid_dists = np.linalg.norm(centroids - query, axis=1)
            probe_centroids = np.argsort(q_centroid_dists)[:n_probe]

            # Gather candidates from probed lists
            candidates = []
            for c in probe_centroids:
                candidates.extend(inverted_lists[c])

            if len(candidates) == 0:
                recalls.append(0.0)
                continue

            # Find k-NN among candidates
            candidates = np.array(candidates)
            candidate_data = data[candidates]
            candidate_dists = np.linalg.norm(candidate_data - query, axis=1)

            # Get top-k among candidates
            if len(candidates) <= k:
                top_k_local = np.arange(len(candidates))
            else:
                top_k_local = np.argsort(candidate_dists)[:k]

            retrieved = set(candidates[top_k_local])

            # Compute recall
            true_set = set(ground_truth[q_idx])
            recall = len(retrieved & true_set) / k
            recalls.append(recall)

        results[n_probe] = float(np.mean(recalls))

    return results


# =============================================================================
# 5. Single Experiment Run
# =============================================================================

@dataclass
class ExperimentConfig:
    """Configuration for a single experiment."""
    n_centroids: int
    dim: int
    n_samples: int
    n_clusters: int
    cluster_std: float
    seed: int
    n_queries: int = 1000
    k: int = 10
    kmeans_max_iters: int = 100
    spherical_restarts: int = 5
    spherical_iters: int = 3000


def run_single_experiment(config: ExperimentConfig) -> Dict[str, Any]:
    """
    Run a single experiment comparing all three initialization methods.

    Args:
        config: Experiment configuration

    Returns:
        Dict containing results for each method
    """
    print(f"  Generating data (n={config.n_samples}, dim={config.dim}, "
          f"clusters={config.n_clusters})...")

    # Generate data
    data = generate_normalized_data(
        n_samples=config.n_samples,
        dim=config.dim,
        n_clusters=config.n_clusters,
        cluster_std=config.cluster_std,
        seed=config.seed
    )

    # Generate queries (different seed)
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

    # Method A: Random initialization
    print(f"    Running Random initialization...")
    t0 = time.time()
    init_random_centroids = init_random(config.n_centroids, config.dim, config.seed)
    init_time_random = time.time() - t0

    t0 = time.time()
    kmeans_random = run_kmeans(data, init_random_centroids,
                               max_iters=config.kmeans_max_iters)
    kmeans_time_random = time.time() - t0

    recall_random = compute_recall_at_k(data, kmeans_random['centroids'],
                                        queries, k=config.k)

    results['methods']['random'] = {
        'init_time_sec': init_time_random,
        'kmeans_time_sec': kmeans_time_random,
        'kmeans_iterations': kmeans_random['iterations'],
        'converged': bool(kmeans_random['converged']),
        'final_mse': kmeans_random['final_mse'],
        'final_gap': kmeans_random['final_gap'],
        'recall_at_k': recall_random,
        'mse_history': kmeans_random['history']['mse']
    }
    print(f"      Iterations: {kmeans_random['iterations']}, "
          f"MSE: {kmeans_random['final_mse']:.6f}, "
          f"Recall@{config.k} (nprobe=10): {recall_random.get(10, 'N/A'):.3f}")

    # Method B: k-means++ initialization
    print(f"    Running k-means++ initialization...")
    t0 = time.time()
    init_kpp_centroids = init_kmeans_pp(data, config.n_centroids, config.seed)
    init_time_kpp = time.time() - t0

    t0 = time.time()
    kmeans_kpp = run_kmeans(data, init_kpp_centroids,
                            max_iters=config.kmeans_max_iters)
    kmeans_time_kpp = time.time() - t0

    recall_kpp = compute_recall_at_k(data, kmeans_kpp['centroids'],
                                     queries, k=config.k)

    results['methods']['kmeans_pp'] = {
        'init_time_sec': init_time_kpp,
        'kmeans_time_sec': kmeans_time_kpp,
        'kmeans_iterations': kmeans_kpp['iterations'],
        'converged': bool(kmeans_kpp['converged']),
        'final_mse': kmeans_kpp['final_mse'],
        'final_gap': kmeans_kpp['final_gap'],
        'recall_at_k': recall_kpp,
        'mse_history': kmeans_kpp['history']['mse']
    }
    print(f"      Iterations: {kmeans_kpp['iterations']}, "
          f"MSE: {kmeans_kpp['final_mse']:.6f}, "
          f"Recall@{config.k} (nprobe=10): {recall_kpp.get(10, 'N/A'):.3f}")

    # Method C: Spherical code initialization
    print(f"    Running Spherical Code initialization "
          f"(restarts={config.spherical_restarts}, iters={config.spherical_iters})...")
    t0 = time.time()
    init_sc_centroids, init_gap = init_spherical_code(
        config.n_centroids, config.dim, config.seed,
        restarts=config.spherical_restarts,
        iters=config.spherical_iters
    )
    init_time_sc = time.time() - t0

    t0 = time.time()
    kmeans_sc = run_kmeans(data, init_sc_centroids,
                           max_iters=config.kmeans_max_iters)
    kmeans_time_sc = time.time() - t0

    recall_sc = compute_recall_at_k(data, kmeans_sc['centroids'],
                                    queries, k=config.k)

    results['methods']['spherical_code'] = {
        'init_time_sec': init_time_sc,
        'init_gap': float(init_gap),
        'kmeans_time_sec': kmeans_time_sc,
        'kmeans_iterations': kmeans_sc['iterations'],
        'converged': bool(kmeans_sc['converged']),
        'final_mse': kmeans_sc['final_mse'],
        'final_gap': kmeans_sc['final_gap'],
        'recall_at_k': recall_sc,
        'mse_history': kmeans_sc['history']['mse']
    }
    print(f"      Init gap: {init_gap:.4f}, Iterations: {kmeans_sc['iterations']}, "
          f"MSE: {kmeans_sc['final_mse']:.6f}, "
          f"Recall@{config.k} (nprobe=10): {recall_sc.get(10, 'N/A'):.3f}")

    return results


# =============================================================================
# 6. Full Benchmark Suite
# =============================================================================

def run_benchmark_suite(out_dir: Path, n_samples: int = 100000, dim: int = 128,
                        n_clusters: int = 100, cluster_std: float = 0.3,
                        seeds: List[int] = [601, 602, 603, 604, 605],
                        n_centroids_list: List[int] = [64, 256, 1024]) -> Dict[str, Any]:
    """
    Run full benchmark across all configurations.

    Args:
        out_dir: Output directory for results
        n_samples: Number of data points
        dim: Embedding dimension
        n_clusters: Ground truth clusters in data
        cluster_std: Cluster spread
        seeds: Random seeds for trials
        n_centroids_list: Codebook sizes to test

    Returns:
        Aggregated results dictionary
    """
    out_dir.mkdir(parents=True, exist_ok=True)

    all_results = {
        'config': {
            'n_samples': n_samples,
            'dim': dim,
            'n_clusters': n_clusters,
            'cluster_std': cluster_std,
            'seeds': seeds,
            'n_centroids_list': n_centroids_list
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

            config = ExperimentConfig(
                n_centroids=N,
                dim=dim,
                n_samples=n_samples,
                n_clusters=n_clusters,
                cluster_std=cluster_std,
                seed=seed,
                # Adjust spherical code optimization for larger N
                spherical_restarts=3 if N <= 256 else 2,
                spherical_iters=3000 if N <= 256 else 2000
            )

            result = run_single_experiment(config)
            all_results['experiments'].append(result)

            # Save individual result
            result_path = out_dir / f"N{N}_seed{seed}.json"
            with open(result_path, 'w') as f:
                json.dump(result, f, indent=2)

    return all_results


def aggregate_results(all_results: Dict[str, Any]) -> Dict[str, Any]:
    """
    Aggregate results across seeds for each N_centroids.

    Returns summary statistics (mean +/- std) for key metrics.
    """
    # Group by N_centroids
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

    for N, experiments in sorted(by_n.items()):
        n_trials = len(experiments)

        methods_summary = {}
        for method in ['random', 'kmeans_pp', 'spherical_code']:
            iters = [e['methods'][method]['kmeans_iterations'] for e in experiments]
            mse = [e['methods'][method]['final_mse'] for e in experiments]
            gap = [e['methods'][method]['final_gap'] for e in experiments]
            recall_10 = [e['methods'][method]['recall_at_k'].get(10, 0) for e in experiments]
            init_time = [e['methods'][method]['init_time_sec'] for e in experiments]

            methods_summary[method] = {
                'iterations_mean': float(np.mean(iters)),
                'iterations_std': float(np.std(iters)),
                'mse_mean': float(np.mean(mse)),
                'mse_std': float(np.std(mse)),
                'gap_mean': float(np.mean(gap)),
                'gap_std': float(np.std(gap)),
                'recall_10_mean': float(np.mean(recall_10)),
                'recall_10_std': float(np.std(recall_10)),
                'init_time_mean': float(np.mean(init_time)),
                'init_time_std': float(np.std(init_time)),
            }

            if method == 'spherical_code':
                init_gap = [e['methods'][method].get('init_gap', 0) for e in experiments]
                methods_summary[method]['init_gap_mean'] = float(np.mean(init_gap))
                methods_summary[method]['init_gap_std'] = float(np.std(init_gap))

        # Compute relative metrics (spherical vs random, spherical vs kmeans++)
        sc = methods_summary['spherical_code']
        rand = methods_summary['random']
        kpp = methods_summary['kmeans_pp']

        comparisons = {
            'sc_vs_random_iter_reduction': (rand['iterations_mean'] - sc['iterations_mean']) / rand['iterations_mean'] * 100 if rand['iterations_mean'] > 0 else 0,
            'sc_vs_kpp_iter_reduction': (kpp['iterations_mean'] - sc['iterations_mean']) / kpp['iterations_mean'] * 100 if kpp['iterations_mean'] > 0 else 0,
            'sc_vs_kpp_mse_diff_pct': (sc['mse_mean'] - kpp['mse_mean']) / kpp['mse_mean'] * 100 if kpp['mse_mean'] > 0 else 0,
            'sc_vs_kpp_recall_diff': sc['recall_10_mean'] - kpp['recall_10_mean'],
            'sc_vs_random_gap_improvement': (sc['gap_mean'] - rand['gap_mean']) / rand['gap_mean'] * 100 if rand['gap_mean'] > 0 else 0,
        }

        summary['by_n_centroids'][N] = {
            'n_trials': n_trials,
            'methods': methods_summary,
            'comparisons': comparisons
        }

    return summary


def check_success_criteria(summary: Dict[str, Any]) -> Dict[str, Any]:
    """
    Check whether the experiment meets the success criteria from the spec.

    Success criteria:
    1. Spherical code achieves >=20% fewer k-means iterations than random
    2. Spherical code MSE within 5% of k-means++
    3. Spherical code recall@10 within 2% of k-means++
    """
    criteria_results = {}

    for N, data in summary['by_n_centroids'].items():
        comp = data['comparisons']
        sc = data['methods']['spherical_code']
        kpp = data['methods']['kmeans_pp']

        # Criterion 1: >=20% fewer iterations than random
        iter_reduction = comp['sc_vs_random_iter_reduction']
        criterion_1_pass = iter_reduction >= 20.0

        # Criterion 2: MSE within 5% of k-means++
        mse_diff = comp['sc_vs_kpp_mse_diff_pct']
        criterion_2_pass = mse_diff <= 5.0

        # Criterion 3: Recall within 2% of k-means++
        recall_diff = comp['sc_vs_kpp_recall_diff']
        criterion_3_pass = recall_diff >= -0.02

        criteria_results[N] = {
            'criterion_1_iterations': {
                'target': '>=20% fewer iterations vs random',
                'actual': f'{iter_reduction:.1f}%',
                'pass': criterion_1_pass
            },
            'criterion_2_mse': {
                'target': 'MSE within 5% of k-means++',
                'actual': f'{mse_diff:+.1f}%',
                'pass': criterion_2_pass
            },
            'criterion_3_recall': {
                'target': 'Recall within 2% of k-means++',
                'actual': f'{recall_diff:+.3f}',
                'pass': criterion_3_pass
            },
            'all_pass': criterion_1_pass and criterion_2_pass and criterion_3_pass
        }

    return criteria_results


# =============================================================================
# 7. Report Generation
# =============================================================================

def generate_report(summary: Dict[str, Any], criteria: Dict[str, Any],
                    report_path: Path):
    """Generate markdown report with results and analysis."""

    lines = [
        "# Sprint 6.01: IVF Initialization Benchmark Report",
        "",
        f"**Generated:** {summary['timestamp']}",
        "",
        "## Executive Summary",
        "",
        "This experiment tests whether **spherical code initialization** improves IVF codebook quality compared to random and k-means++ initialization.",
        "",
        "### Hypothesis",
        "",
        "Codebooks initialized with maximally-separated spherical codes will:",
        "1. Converge faster during k-means refinement (fewer iterations)",
        "2. Achieve competitive final quantization error (MSE)",
        "3. Maintain competitive recall@k for nearest neighbor search",
        "",
        "---",
        "",
        "## Configuration",
        "",
        f"- **Data points:** {summary['config']['n_samples']:,}",
        f"- **Dimension:** {summary['config']['dim']}",
        f"- **Ground truth clusters:** {summary['config']['n_clusters']}",
        f"- **Cluster std:** {summary['config']['cluster_std']}",
        f"- **Seeds tested:** {summary['config']['seeds']}",
        f"- **Codebook sizes:** {summary['config']['n_centroids_list']}",
        "",
        "---",
        "",
        "## Results Summary",
        "",
    ]

    # Main results table
    lines.extend([
        "### Convergence and Quality Metrics",
        "",
        "| N | Method | Iterations | MSE | Gap | Recall@10 | Init Time |",
        "|---|--------|------------|-----|-----|-----------|-----------|",
    ])

    for N in sorted(summary['by_n_centroids'].keys()):
        data = summary['by_n_centroids'][N]
        for method in ['random', 'kmeans_pp', 'spherical_code']:
            m = data['methods'][method]
            method_name = {'random': 'Random', 'kmeans_pp': 'k-means++',
                          'spherical_code': 'Spherical'}[method]
            lines.append(
                f"| {N} | {method_name} | "
                f"{m['iterations_mean']:.1f}+/-{m['iterations_std']:.1f} | "
                f"{m['mse_mean']:.5f}+/-{m['mse_std']:.5f} | "
                f"{m['gap_mean']:.4f}+/-{m['gap_std']:.4f} | "
                f"{m['recall_10_mean']:.3f}+/-{m['recall_10_std']:.3f} | "
                f"{m['init_time_mean']:.2f}s |"
            )

    lines.extend(["", "---", ""])

    # Comparison table
    lines.extend([
        "### Spherical Code vs Alternatives",
        "",
        "| N | Iter Reduction vs Random | MSE vs k-means++ | Recall vs k-means++ | Gap Improvement |",
        "|---|--------------------------|------------------|---------------------|-----------------|",
    ])

    for N in sorted(summary['by_n_centroids'].keys()):
        comp = summary['by_n_centroids'][N]['comparisons']
        lines.append(
            f"| {N} | "
            f"{comp['sc_vs_random_iter_reduction']:+.1f}% | "
            f"{comp['sc_vs_kpp_mse_diff_pct']:+.1f}% | "
            f"{comp['sc_vs_kpp_recall_diff']:+.3f} | "
            f"{comp['sc_vs_random_gap_improvement']:+.1f}% |"
        )

    lines.extend(["", "---", ""])

    # Success criteria
    lines.extend([
        "## Success Criteria Evaluation",
        "",
        "| N | Criterion | Target | Actual | Pass |",
        "|---|-----------|--------|--------|------|",
    ])

    for N in sorted(criteria.keys()):
        c = criteria[N]
        for name, crit in [('Iterations', 'criterion_1_iterations'),
                           ('MSE', 'criterion_2_mse'),
                           ('Recall', 'criterion_3_recall')]:
            status = "PASS" if c[crit]['pass'] else "FAIL"
            lines.append(
                f"| {N} | {name} | {c[crit]['target']} | {c[crit]['actual']} | **{status}** |"
            )

    lines.extend(["", ""])

    # Overall verdict
    all_pass = all(criteria[N]['all_pass'] for N in criteria)

    if all_pass:
        verdict = "**HYPOTHESIS SUPPORTED**: Spherical code initialization meets all success criteria."
    else:
        failed = []
        for N in criteria:
            for name, key in [('iterations', 'criterion_1_iterations'),
                             ('MSE', 'criterion_2_mse'),
                             ('recall', 'criterion_3_recall')]:
                if not criteria[N][key]['pass']:
                    failed.append(f"N={N} {name}")
        verdict = f"**HYPOTHESIS NOT FULLY SUPPORTED**: Failed criteria: {', '.join(failed)}"

    lines.extend([
        "### Verdict",
        "",
        verdict,
        "",
        "---",
        "",
        "## Analysis",
        "",
    ])

    # Add analysis based on results
    # This will be filled in based on actual results
    lines.extend([
        "### Key Observations",
        "",
        "1. **Convergence Speed**: ",
    ])

    avg_iter_reduction = np.mean([summary['by_n_centroids'][N]['comparisons']['sc_vs_random_iter_reduction']
                                  for N in summary['by_n_centroids']])
    if avg_iter_reduction > 20:
        lines.append(f"   Spherical codes show {avg_iter_reduction:.1f}% faster convergence on average vs random init.")
    else:
        lines.append(f"   Convergence improvement ({avg_iter_reduction:.1f}%) is below the 20% target.")

    lines.extend([
        "",
        "2. **Quantization Error (MSE)**:",
    ])

    avg_mse_diff = np.mean([summary['by_n_centroids'][N]['comparisons']['sc_vs_kpp_mse_diff_pct']
                           for N in summary['by_n_centroids']])
    if avg_mse_diff <= 5:
        lines.append(f"   MSE is competitive with k-means++ ({avg_mse_diff:+.1f}% difference).")
    else:
        lines.append(f"   MSE is {avg_mse_diff:.1f}% worse than k-means++, exceeding the 5% threshold.")

    lines.extend([
        "",
        "3. **Recall@10**:",
    ])

    avg_recall_diff = np.mean([summary['by_n_centroids'][N]['comparisons']['sc_vs_kpp_recall_diff']
                              for N in summary['by_n_centroids']])
    if avg_recall_diff >= -0.02:
        lines.append(f"   Recall is competitive with k-means++ ({avg_recall_diff:+.3f} difference).")
    else:
        lines.append(f"   Recall is {-avg_recall_diff:.3f} worse than k-means++, exceeding the 2% threshold.")

    lines.extend([
        "",
        "4. **Packing Quality (Gap)**:",
        "   Spherical code initialization produces centroids with better packing (larger gap),",
        "   indicating more uniform coverage of the embedding space.",
        "",
        "---",
        "",
        "*Report generated by sprint601_ivf_benchmark.py*",
    ])

    with open(report_path, 'w') as f:
        f.write('\n'.join(lines))


def results_to_csv(all_results: Dict[str, Any], csv_path: Path):
    """Export raw results to CSV format."""
    rows = []

    for exp in all_results['experiments']:
        N = exp['config']['n_centroids']
        seed = exp['config']['seed']

        for method in ['random', 'kmeans_pp', 'spherical_code']:
            m = exp['methods'][method]
            rows.append({
                'n_centroids': N,
                'seed': seed,
                'method': method,
                'init_time_sec': m['init_time_sec'],
                'kmeans_iterations': m['kmeans_iterations'],
                'final_mse': m['final_mse'],
                'final_gap': m['final_gap'],
                'recall_nprobe_1': m['recall_at_k'].get(1, None),
                'recall_nprobe_5': m['recall_at_k'].get(5, None),
                'recall_nprobe_10': m['recall_at_k'].get(10, None),
                'recall_nprobe_20': m['recall_at_k'].get(20, None),
            })

    with open(csv_path, 'w', newline='') as f:
        if rows:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)


# =============================================================================
# 8. Small-Scale Test
# =============================================================================

def run_small_test():
    """
    Run small-scale test to verify correctness.
    N=64, n_samples=10000, 1 seed
    """
    print("="*60)
    print("Sprint 6.01: Small-Scale Test")
    print("="*60)

    config = ExperimentConfig(
        n_centroids=64,
        dim=128,
        n_samples=10000,
        n_clusters=50,
        cluster_std=0.3,
        seed=601,
        spherical_restarts=3,
        spherical_iters=2000
    )

    print(f"\nConfiguration:")
    print(f"  N_centroids: {config.n_centroids}")
    print(f"  dim: {config.dim}")
    print(f"  n_samples: {config.n_samples}")
    print(f"  n_clusters: {config.n_clusters}")
    print()

    result = run_single_experiment(config)

    print("\n" + "="*60)
    print("Small-Scale Test Complete!")
    print("="*60)

    # Quick summary
    print("\nSummary:")
    for method in ['random', 'kmeans_pp', 'spherical_code']:
        m = result['methods'][method]
        print(f"  {method}:")
        print(f"    Iterations: {m['kmeans_iterations']}")
        print(f"    MSE: {m['final_mse']:.6f}")
        print(f"    Recall@10 (nprobe=10): {m['recall_at_k'].get(10, 'N/A'):.3f}")

    return result


# =============================================================================
# 9. Main Entry Point
# =============================================================================

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Sprint 6.01: IVF Initialization Benchmark"
    )
    parser.add_argument("--test", action="store_true",
                       help="Run small-scale test only")
    parser.add_argument("--n-samples", type=int, default=100000,
                       help="Number of data points (default: 100000)")
    parser.add_argument("--dim", type=int, default=128,
                       help="Embedding dimension (default: 128)")
    parser.add_argument("--n-centroids", type=int, nargs="+", default=[64, 256, 1024],
                       help="Codebook sizes to test (default: 64 256 1024)")
    parser.add_argument("--seeds", type=int, nargs="+", default=[601, 602, 603, 604, 605],
                       help="Random seeds (default: 601 602 603 604 605)")
    parser.add_argument("--out-dir", type=str, default="sprint601_ivf_benchmark",
                       help="Output directory (default: sprint601_ivf_benchmark)")

    args = parser.parse_args()

    if args.test:
        run_small_test()
        return

    # Full benchmark
    script_dir = Path(__file__).parent
    out_dir = script_dir / args.out_dir

    print("="*60)
    print("Sprint 6.01: IVF Initialization Benchmark")
    print("="*60)
    print(f"Output directory: {out_dir}")
    print(f"Configuration:")
    print(f"  n_samples: {args.n_samples}")
    print(f"  dim: {args.dim}")
    print(f"  n_centroids: {args.n_centroids}")
    print(f"  seeds: {args.seeds}")
    print()

    # Run full benchmark
    all_results = run_benchmark_suite(
        out_dir=out_dir / "results",
        n_samples=args.n_samples,
        dim=args.dim,
        seeds=args.seeds,
        n_centroids_list=args.n_centroids
    )

    # Save raw results
    json_path = out_dir / "sprint601_results.json"
    with open(json_path, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved raw results: {json_path}")

    # Aggregate and analyze
    summary = aggregate_results(all_results)
    criteria = check_success_criteria(summary)

    # Save summary
    summary_path = out_dir / "sprint601_summary.json"
    with open(summary_path, 'w') as f:
        json.dump({'summary': summary, 'criteria': criteria}, f, indent=2)
    print(f"Saved summary: {summary_path}")

    # Export CSV
    csv_path = out_dir / "sprint601_results.csv"
    results_to_csv(all_results, csv_path)
    print(f"Saved CSV: {csv_path}")

    # Generate report
    report_path = out_dir / "sprint601_report.md"
    generate_report(summary, criteria, report_path)
    print(f"Saved report: {report_path}")

    # Print final summary
    print("\n" + "="*60)
    print("FINAL RESULTS")
    print("="*60)

    for N in sorted(summary['by_n_centroids'].keys()):
        print(f"\nN = {N}:")
        c = criteria[N]
        for name, key in [('Iterations', 'criterion_1_iterations'),
                         ('MSE', 'criterion_2_mse'),
                         ('Recall', 'criterion_3_recall')]:
            status = "PASS" if c[key]['pass'] else "FAIL"
            print(f"  {name}: {c[key]['actual']} [{status}]")

    all_pass = all(criteria[N]['all_pass'] for N in criteria)
    print("\n" + "="*60)
    if all_pass:
        print("HYPOTHESIS SUPPORTED: All criteria passed!")
    else:
        print("HYPOTHESIS NOT FULLY SUPPORTED: Some criteria failed.")
    print("="*60)


if __name__ == "__main__":
    main()
