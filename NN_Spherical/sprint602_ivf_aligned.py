"""
Sprint 6.02: Data-Aligned Spherical Code Initialization
========================================================
Tests whether rotation alignment fixes the convergence problem from Sprint 6.01.

Key insight: Rotation is isometric - it preserves pairwise distances (and gap),
but can reorient the spherical code to better match the data distribution.

Author: R.J. Mathews
Date: 2026-01-30
Prerequisite: Sprint 6.01 (completed)
"""

import numpy as np
import json
import csv
import time
from dataclasses import dataclass, asdict
from typing import Dict, List, Tuple, Any
from pathlib import Path

# Import from Sprint 6.01
from sprint601_ivf_benchmark import (
    generate_normalized_data,
    init_random,
    init_kmeans_pp,
    init_spherical_code,
    run_kmeans,
    compute_recall_at_k,
    ExperimentConfig
)


# =============================================================================
# 1. Alignment Strategies
# =============================================================================

def compute_gap(centroids: np.ndarray) -> float:
    """Compute minimum pairwise distance (gap) between centroids."""
    dists = np.linalg.norm(centroids[:, None, :] - centroids[None, :, :], axis=2)
    np.fill_diagonal(dists, np.inf)
    return float(np.min(dists))


def align_pca(spherical_code: np.ndarray, data: np.ndarray) -> np.ndarray:
    """
    Rotate spherical code so its principal components align with data PCs.

    Rationale: Data variance directions should match codebook spread directions.
    This is a pure rotation (orthogonal transform), so distances are preserved.

    Args:
        spherical_code: (N, dim) spherical code centroids
        data: (n_samples, dim) data points

    Returns:
        Rotated spherical code (N, dim) on unit sphere
    """
    N, dim = spherical_code.shape

    # Compute principal components of data (full_matrices=True for full rotation)
    data_centered = data - data.mean(axis=0)
    _, _, Vt_data = np.linalg.svd(data_centered, full_matrices=True)
    Vt_data = Vt_data[:dim, :]  # (dim, dim)

    # Compute principal components of spherical code
    # Need to use covariance matrix approach for underdetermined case (N < dim)
    code_centered = spherical_code - spherical_code.mean(axis=0)
    cov_code = code_centered.T @ code_centered / N  # (dim, dim)
    eigvals, eigvecs = np.linalg.eigh(cov_code)
    # Sort by eigenvalue descending
    idx = np.argsort(eigvals)[::-1]
    Vt_code = eigvecs[:, idx].T  # (dim, dim)

    # Rotation matrix: align code PCs to data PCs
    # R = Vt_data.T @ Vt_code maps code PC basis to data PC basis
    R = Vt_data.T @ Vt_code

    # Apply rotation (rotate each centroid)
    rotated = spherical_code @ R.T

    # Re-normalize to unit sphere (should be very close already due to orthogonality)
    norms = np.linalg.norm(rotated, axis=1, keepdims=True)
    rotated = rotated / np.maximum(norms, 1e-12)

    return rotated.astype(np.float32)


def align_procrustes(spherical_code: np.ndarray, target: np.ndarray) -> np.ndarray:
    """
    Orthogonal Procrustes: find rotation R minimizing ||spherical_code @ R - target||_F

    Rationale: Align spherical code to k-means++ positions which are data-aware.

    Args:
        spherical_code: (N, dim) spherical code centroids
        target: (N, dim) target positions (e.g., k-means++ initialization)

    Returns:
        Rotated spherical code (N, dim) on unit sphere
    """
    # Solve Procrustes: minimize ||A @ R - B||_F
    # Solution: R = V @ U.T where B.T @ A = U @ S @ V.T
    M = target.T @ spherical_code
    U, _, Vt = np.linalg.svd(M)
    R = U @ Vt

    # Ensure proper rotation (det = 1, not reflection)
    if np.linalg.det(R) < 0:
        # Flip sign of last column to fix reflection
        U[:, -1] *= -1
        R = U @ Vt

    # Apply rotation
    rotated = spherical_code @ R.T

    # Re-normalize
    norms = np.linalg.norm(rotated, axis=1, keepdims=True)
    rotated = rotated / np.maximum(norms, 1e-12)

    return rotated.astype(np.float32)


def align_to_clusters(spherical_code: np.ndarray, data: np.ndarray,
                      n_sample: int = 10000, n_quick_iters: int = 10,
                      seed: int = 42) -> np.ndarray:
    """
    Quick clustering on data sample, then Procrustes align to cluster centers.

    Rationale: Get approximate data structure cheaply, align spherical code to it.
    This avoids the full cost of k-means++ while still getting data awareness.

    Args:
        spherical_code: (N, dim) spherical code centroids
        data: (n_samples, dim) data points
        n_sample: Number of data points to subsample
        n_quick_iters: Number of quick k-means iterations
        seed: Random seed

    Returns:
        Rotated spherical code (N, dim) on unit sphere
    """
    rng = np.random.default_rng(seed)
    N, dim = spherical_code.shape

    # Subsample for speed
    n_use = min(n_sample, len(data))
    idx = rng.choice(len(data), n_use, replace=False)
    sample = data[idx]

    # Initialize centers randomly from sample
    center_idx = rng.choice(n_use, N, replace=False)
    centers = sample[center_idx].copy()

    # Quick k-means (few iterations, just to find rough centers)
    for _ in range(n_quick_iters):
        # Assignment using dot product for efficiency
        dots = sample @ centers.T
        dots = np.clip(dots, -1.0, 1.0)
        sq_dists = 2.0 * (1.0 - dots)
        assignments = np.argmin(sq_dists, axis=1)

        # Update centers
        new_centers = np.zeros_like(centers)
        counts = np.zeros(N)
        for d in range(dim):
            new_centers[:, d] = np.bincount(assignments, weights=sample[:, d], minlength=N)
        counts = np.bincount(assignments, minlength=N).astype(float)

        # Handle empty clusters
        empty = counts == 0
        if np.any(empty):
            empty_idx = np.where(empty)[0]
            for i in empty_idx:
                new_centers[i] = sample[rng.integers(n_use)]
                counts[i] = 1

        new_centers = new_centers / counts[:, None]

        # Normalize to unit sphere
        norms = np.linalg.norm(new_centers, axis=1, keepdims=True)
        centers = new_centers / np.maximum(norms, 1e-12)

    # Procrustes align spherical code to these rough centers
    return align_procrustes(spherical_code, centers)


# =============================================================================
# 2. Extended Initialization Methods
# =============================================================================

def init_spherical_pca(N: int, dim: int, data: np.ndarray, seed: int,
                       restarts: int = 5, iters: int = 3000) -> Tuple[np.ndarray, float, float]:
    """
    Generate spherical code and align with PCA.

    Returns:
        centroids: Aligned centroids
        init_gap: Gap before alignment
        final_gap: Gap after alignment (should be ~same)
    """
    spherical, init_gap = init_spherical_code(N, dim, seed, restarts, iters)
    aligned = align_pca(spherical, data)
    final_gap = compute_gap(aligned)
    return aligned, init_gap, final_gap


def init_spherical_procrustes(N: int, dim: int, data: np.ndarray, seed: int,
                              restarts: int = 5, iters: int = 3000) -> Tuple[np.ndarray, float, float, np.ndarray]:
    """
    Generate spherical code and align with Procrustes to k-means++ positions.

    Returns:
        centroids: Aligned centroids
        init_gap: Gap before alignment
        final_gap: Gap after alignment
        kpp_centroids: The k-means++ centroids used as target
    """
    spherical, init_gap = init_spherical_code(N, dim, seed, restarts, iters)
    kpp_centroids = init_kmeans_pp(data, N, seed)
    aligned = align_procrustes(spherical, kpp_centroids)
    final_gap = compute_gap(aligned)
    return aligned, init_gap, final_gap, kpp_centroids


def init_spherical_cluster(N: int, dim: int, data: np.ndarray, seed: int,
                           restarts: int = 5, iters: int = 3000) -> Tuple[np.ndarray, float, float]:
    """
    Generate spherical code and align with quick cluster matching.

    Returns:
        centroids: Aligned centroids
        init_gap: Gap before alignment
        final_gap: Gap after alignment
    """
    spherical, init_gap = init_spherical_code(N, dim, seed, restarts, iters)
    aligned = align_to_clusters(spherical, data, seed=seed)
    final_gap = compute_gap(aligned)
    return aligned, init_gap, final_gap


# =============================================================================
# 3. Sanity Check
# =============================================================================

def run_sanity_check():
    """
    Verify that rotation preserves gap before running full experiment.
    If gap drops significantly (< 95%), rotation is breaking geometry.
    """
    print("="*60)
    print("Sprint 6.02: Gap Preservation Sanity Check")
    print("="*60)

    # Generate test data
    print("\nGenerating test data (n=10000, dim=128)...")
    data = generate_normalized_data(10000, 128, 50, 0.3, seed=42)

    # Generate spherical code
    print("Generating spherical code (N=64)...")
    spherical, init_gap = init_spherical_code(64, 128, seed=42, restarts=3, iters=2000)
    gap_before = compute_gap(spherical)

    print(f"\nUnrotated spherical code:")
    print(f"  Gap: {gap_before:.4f}")

    # Test each alignment method
    results = {}

    print("\nTesting PCA alignment...")
    aligned_pca = align_pca(spherical, data)
    gap_pca = compute_gap(aligned_pca)
    pct_pca = gap_pca / gap_before * 100
    results['pca'] = {'gap': gap_pca, 'preserved_pct': pct_pca}
    print(f"  Gap after PCA: {gap_pca:.4f} ({pct_pca:.1f}% preserved)")

    print("\nTesting Procrustes alignment...")
    kpp = init_kmeans_pp(data, 64, seed=42)
    aligned_proc = align_procrustes(spherical, kpp)
    gap_proc = compute_gap(aligned_proc)
    pct_proc = gap_proc / gap_before * 100
    results['procrustes'] = {'gap': gap_proc, 'preserved_pct': pct_proc}
    print(f"  Gap after Procrustes: {gap_proc:.4f} ({pct_proc:.1f}% preserved)")

    print("\nTesting Cluster alignment...")
    aligned_cluster = align_to_clusters(spherical, data, seed=42)
    gap_cluster = compute_gap(aligned_cluster)
    pct_cluster = gap_cluster / gap_before * 100
    results['cluster'] = {'gap': gap_cluster, 'preserved_pct': pct_cluster}
    print(f"  Gap after Cluster: {gap_cluster:.4f} ({pct_cluster:.1f}% preserved)")

    # Verdict
    print("\n" + "="*60)
    all_preserved = all(r['preserved_pct'] >= 95 for r in results.values())

    if all_preserved:
        print("SANITY CHECK PASSED: All alignments preserve gap >= 95%")
        print("Proceeding with full experiment is safe.")
    else:
        print("WARNING: Some alignments break gap preservation:")
        for method, r in results.items():
            if r['preserved_pct'] < 95:
                print(f"  {method}: only {r['preserved_pct']:.1f}% preserved")
        print("Review alignment implementations before proceeding.")

    print("="*60)

    return all_preserved, results


# =============================================================================
# 4. Single Experiment Run
# =============================================================================

def run_single_experiment_aligned(config: ExperimentConfig) -> Dict[str, Any]:
    """
    Run experiment comparing all initialization methods including aligned versions.
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

    # Helper to run k-means and compute recall
    def evaluate_init(name: str, init_centroids: np.ndarray,
                      init_time: float, extra_data: dict = None):
        init_gap = compute_gap(init_centroids)

        t0 = time.time()
        kmeans_result = run_kmeans(data, init_centroids, max_iters=config.kmeans_max_iters)
        kmeans_time = time.time() - t0

        recall = compute_recall_at_k(data, kmeans_result['centroids'], queries, k=config.k)

        result = {
            'init_time_sec': init_time,
            'init_gap': init_gap,
            'kmeans_time_sec': kmeans_time,
            'kmeans_iterations': kmeans_result['iterations'],
            'converged': bool(kmeans_result['converged']),
            'final_mse': kmeans_result['final_mse'],
            'final_gap': kmeans_result['final_gap'],
            'recall_at_k': recall
        }
        if extra_data:
            result.update(extra_data)

        results['methods'][name] = result

        print(f"    {name}: Iters={kmeans_result['iterations']}, "
              f"MSE={kmeans_result['final_mse']:.6f}, "
              f"InitGap={init_gap:.4f}, "
              f"Recall@{config.k}={recall.get(10, 0):.3f}")

    # Method 1: Random
    print("    Running Random...")
    t0 = time.time()
    init_random_c = init_random(config.n_centroids, config.dim, config.seed)
    init_time = time.time() - t0
    evaluate_init('random', init_random_c, init_time)

    # Method 2: k-means++
    print("    Running k-means++...")
    t0 = time.time()
    init_kpp = init_kmeans_pp(data, config.n_centroids, config.seed)
    init_time = time.time() - t0
    evaluate_init('kmeans_pp', init_kpp, init_time)

    # Method 3: Spherical (unrotated) - from Sprint 6.01
    print("    Running Spherical (unrotated)...")
    t0 = time.time()
    init_spherical, spherical_gap = init_spherical_code(
        config.n_centroids, config.dim, config.seed,
        restarts=config.spherical_restarts, iters=config.spherical_iters
    )
    init_time = time.time() - t0
    evaluate_init('spherical_unrotated', init_spherical, init_time,
                  {'optimizer_gap': float(spherical_gap)})

    # Method 4: Spherical + PCA alignment
    print("    Running Spherical + PCA...")
    t0 = time.time()
    init_pca, _, gap_after_pca = init_spherical_pca(
        config.n_centroids, config.dim, data, config.seed,
        restarts=config.spherical_restarts, iters=config.spherical_iters
    )
    init_time = time.time() - t0
    evaluate_init('spherical_pca', init_pca, init_time,
                  {'gap_preserved_pct': float(gap_after_pca / compute_gap(init_spherical) * 100)})

    # Method 5: Spherical + Procrustes (to k-means++)
    print("    Running Spherical + Procrustes...")
    t0 = time.time()
    init_proc, _, gap_after_proc, _ = init_spherical_procrustes(
        config.n_centroids, config.dim, data, config.seed,
        restarts=config.spherical_restarts, iters=config.spherical_iters
    )
    init_time = time.time() - t0
    evaluate_init('spherical_procrustes', init_proc, init_time,
                  {'gap_preserved_pct': float(gap_after_proc / compute_gap(init_spherical) * 100)})

    # Method 6: Spherical + Cluster matching
    print("    Running Spherical + Cluster...")
    t0 = time.time()
    init_cluster, _, gap_after_cluster = init_spherical_cluster(
        config.n_centroids, config.dim, data, config.seed,
        restarts=config.spherical_restarts, iters=config.spherical_iters
    )
    init_time = time.time() - t0
    evaluate_init('spherical_cluster', init_cluster, init_time,
                  {'gap_preserved_pct': float(gap_after_cluster / compute_gap(init_spherical) * 100)})

    return results


# =============================================================================
# 5. Benchmark Suite
# =============================================================================

def run_benchmark_suite(out_dir: Path, n_samples: int = 50000, dim: int = 128,
                        n_clusters: int = 100, cluster_std: float = 0.3,
                        seeds: List[int] = [601, 602, 603],
                        n_centroids_list: List[int] = [64, 256]) -> Dict[str, Any]:
    """Run full benchmark across all configurations."""
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
                spherical_restarts=3 if N <= 256 else 2,
                spherical_iters=3000 if N <= 256 else 2000
            )

            result = run_single_experiment_aligned(config)
            all_results['experiments'].append(result)

            # Save individual result
            result_path = out_dir / f"N{N}_seed{seed}.json"
            with open(result_path, 'w') as f:
                json.dump(result, f, indent=2)

    return all_results


# =============================================================================
# 6. Analysis and Reporting
# =============================================================================

def aggregate_results(all_results: Dict[str, Any]) -> Dict[str, Any]:
    """Aggregate results across seeds for each N_centroids."""
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

    methods = ['random', 'kmeans_pp', 'spherical_unrotated',
               'spherical_pca', 'spherical_procrustes', 'spherical_cluster']

    for N, experiments in sorted(by_n.items()):
        n_trials = len(experiments)
        methods_summary = {}

        for method in methods:
            if method not in experiments[0]['methods']:
                continue

            iters = [e['methods'][method]['kmeans_iterations'] for e in experiments]
            mse = [e['methods'][method]['final_mse'] for e in experiments]
            init_gap = [e['methods'][method]['init_gap'] for e in experiments]
            recall_10 = [e['methods'][method]['recall_at_k'].get(10, 0) for e in experiments]
            init_time = [e['methods'][method]['init_time_sec'] for e in experiments]

            methods_summary[method] = {
                'iterations_mean': float(np.mean(iters)),
                'iterations_std': float(np.std(iters)),
                'mse_mean': float(np.mean(mse)),
                'mse_std': float(np.std(mse)),
                'init_gap_mean': float(np.mean(init_gap)),
                'init_gap_std': float(np.std(init_gap)),
                'recall_10_mean': float(np.mean(recall_10)),
                'recall_10_std': float(np.std(recall_10)),
                'init_time_mean': float(np.mean(init_time)),
            }

            # Gap preservation for aligned methods
            if 'gap_preserved_pct' in experiments[0]['methods'][method]:
                gap_pct = [e['methods'][method]['gap_preserved_pct'] for e in experiments]
                methods_summary[method]['gap_preserved_mean'] = float(np.mean(gap_pct))

        # Compute comparisons
        unrotated = methods_summary['spherical_unrotated']
        random_m = methods_summary['random']
        kpp = methods_summary['kmeans_pp']

        comparisons = {}
        for aligned_method in ['spherical_pca', 'spherical_procrustes', 'spherical_cluster']:
            if aligned_method not in methods_summary:
                continue
            aligned = methods_summary[aligned_method]

            # vs unrotated
            iter_vs_unrotated = (unrotated['iterations_mean'] - aligned['iterations_mean']) / unrotated['iterations_mean'] * 100

            # vs random
            iter_vs_random = (random_m['iterations_mean'] - aligned['iterations_mean']) / random_m['iterations_mean'] * 100

            # MSE vs k-means++
            mse_vs_kpp = (aligned['mse_mean'] - kpp['mse_mean']) / kpp['mse_mean'] * 100

            comparisons[aligned_method] = {
                'iter_reduction_vs_unrotated_pct': iter_vs_unrotated,
                'iter_reduction_vs_random_pct': iter_vs_random,
                'mse_diff_vs_kpp_pct': mse_vs_kpp,
                'gap_preserved_pct': aligned.get('gap_preserved_mean', 100.0)
            }

        summary['by_n_centroids'][N] = {
            'n_trials': n_trials,
            'methods': methods_summary,
            'comparisons': comparisons
        }

    return summary


def check_success_criteria(summary: Dict[str, Any]) -> Dict[str, Any]:
    """
    Check Sprint 6.02 success criteria:
    1. Aligned converges >=20% faster than unrotated
    2. Gap preserved >= 95%
    3. MSE within 5% of k-means++
    """
    criteria = {}

    for N, data in summary['by_n_centroids'].items():
        criteria[N] = {}

        for method, comp in data['comparisons'].items():
            # Criterion 1: >=20% faster than unrotated
            iter_reduction = comp['iter_reduction_vs_unrotated_pct']
            c1_pass = iter_reduction >= 20.0

            # Criterion 2: Gap preserved >= 95%
            gap_preserved = comp['gap_preserved_pct']
            c2_pass = gap_preserved >= 95.0

            # Criterion 3: MSE within 5% of k-means++
            mse_diff = comp['mse_diff_vs_kpp_pct']
            c3_pass = mse_diff <= 5.0

            criteria[N][method] = {
                'criterion_1_convergence': {
                    'target': '>=20% fewer iterations vs unrotated',
                    'actual': f'{iter_reduction:+.1f}%',
                    'pass': c1_pass
                },
                'criterion_2_gap': {
                    'target': 'Gap preserved >= 95%',
                    'actual': f'{gap_preserved:.1f}%',
                    'pass': c2_pass
                },
                'criterion_3_mse': {
                    'target': 'MSE within 5% of k-means++',
                    'actual': f'{mse_diff:+.1f}%',
                    'pass': c3_pass
                },
                'all_pass': c1_pass and c2_pass and c3_pass
            }

    return criteria


def generate_report(summary: Dict[str, Any], criteria: Dict[str, Any], report_path: Path):
    """Generate comprehensive markdown report."""
    lines = [
        "# Sprint 6.02: Data-Aligned Spherical Code Initialization",
        "",
        f"**Generated:** {summary['timestamp']}",
        "",
        "## Executive Summary",
        "",
        "This experiment tests whether **rotation alignment** fixes the convergence problem",
        "identified in Sprint 6.01, where spherical codes took 70-145% MORE iterations than random.",
        "",
        "### Hypotheses",
        "",
        "- **H1**: Aligned spherical codes converge faster than unrotated (>=20% improvement)",
        "- **H2**: Rotation preserves separation guarantees (gap >= 95% of original)",
        "- **H3**: Final MSE remains competitive with k-means++ (within 5%)",
        "",
        "---",
        "",
        "## Configuration",
        "",
        f"- **Data points:** {summary['config']['n_samples']:,}",
        f"- **Dimension:** {summary['config']['dim']}",
        f"- **Codebook sizes:** {summary['config']['n_centroids_list']}",
        f"- **Seeds:** {summary['config']['seeds']}",
        "",
        "---",
        "",
        "## Results",
        "",
    ]

    # Main results table
    for N in sorted(summary['by_n_centroids'].keys()):
        data = summary['by_n_centroids'][N]
        lines.extend([
            f"### N = {N} Centroids",
            "",
            "| Method | Iterations | MSE | Init Gap | Recall@10 | Init Time |",
            "|--------|------------|-----|----------|-----------|-----------|",
        ])

        method_names = {
            'random': 'Random',
            'kmeans_pp': 'k-means++',
            'spherical_unrotated': 'Spherical (unrotated)',
            'spherical_pca': 'Spherical + PCA',
            'spherical_procrustes': 'Spherical + Procrustes',
            'spherical_cluster': 'Spherical + Cluster'
        }

        for method in ['random', 'kmeans_pp', 'spherical_unrotated',
                       'spherical_pca', 'spherical_procrustes', 'spherical_cluster']:
            if method not in data['methods']:
                continue
            m = data['methods'][method]
            lines.append(
                f"| {method_names[method]} | "
                f"{m['iterations_mean']:.1f} +/- {m['iterations_std']:.1f} | "
                f"{m['mse_mean']:.5f} | "
                f"{m['init_gap_mean']:.4f} | "
                f"{m['recall_10_mean']:.3f} | "
                f"{m['init_time_mean']:.1f}s |"
            )

        lines.append("")

    # Comparison table
    lines.extend([
        "---",
        "",
        "## Alignment Effect Analysis",
        "",
        "| N | Method | Iter vs Unrotated | Iter vs Random | MSE vs k-means++ | Gap Preserved |",
        "|---|--------|-------------------|----------------|------------------|---------------|",
    ])

    for N in sorted(summary['by_n_centroids'].keys()):
        for method, comp in summary['by_n_centroids'][N]['comparisons'].items():
            method_short = method.replace('spherical_', '')
            lines.append(
                f"| {N} | {method_short} | "
                f"{comp['iter_reduction_vs_unrotated_pct']:+.1f}% | "
                f"{comp['iter_reduction_vs_random_pct']:+.1f}% | "
                f"{comp['mse_diff_vs_kpp_pct']:+.1f}% | "
                f"{comp['gap_preserved_pct']:.1f}% |"
            )

    lines.extend(["", "---", ""])

    # Success criteria
    lines.extend([
        "## Success Criteria Evaluation",
        "",
        "| N | Method | Convergence (H1) | Gap (H2) | MSE (H3) | All Pass |",
        "|---|--------|------------------|----------|----------|----------|",
    ])

    any_all_pass = False
    for N in sorted(criteria.keys()):
        for method, c in criteria[N].items():
            method_short = method.replace('spherical_', '')
            c1 = "PASS" if c['criterion_1_convergence']['pass'] else "FAIL"
            c2 = "PASS" if c['criterion_2_gap']['pass'] else "FAIL"
            c3 = "PASS" if c['criterion_3_mse']['pass'] else "FAIL"
            all_p = "**YES**" if c['all_pass'] else "no"
            if c['all_pass']:
                any_all_pass = True
            lines.append(f"| {N} | {method_short} | {c1} | {c2} | {c3} | {all_p} |")

    lines.extend(["", ""])

    # Verdict
    if any_all_pass:
        verdict = "**HYPOTHESIS SUPPORTED**: At least one alignment method meets all success criteria."
    else:
        verdict = "**HYPOTHESIS NOT SUPPORTED**: No alignment method meets all success criteria."

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

    # Dynamic interpretation based on results
    # Check if alignment helped convergence at all
    helped_convergence = False
    for N in summary['by_n_centroids']:
        for method, comp in summary['by_n_centroids'][N]['comparisons'].items():
            if comp['iter_reduction_vs_unrotated_pct'] > 0:
                helped_convergence = True

    if helped_convergence:
        lines.extend([
            "### Alignment Does Help (Partially)",
            "",
            "Rotation alignment reduces iteration count compared to unrotated spherical codes.",
            "This confirms that **orientation was part of the problem** in Sprint 6.01.",
            "",
        ])
    else:
        lines.extend([
            "### Alignment Does NOT Help",
            "",
            "Rotation alignment does not significantly reduce iteration count.",
            "This suggests the problem is **fundamental objective mismatch**, not just orientation.",
            "Packing (maximizing separation) is not the same as clustering (minimizing quantization error).",
            "",
        ])

    # Check gap preservation
    gaps_preserved = True
    for N in summary['by_n_centroids']:
        for method, comp in summary['by_n_centroids'][N]['comparisons'].items():
            if comp['gap_preserved_pct'] < 95:
                gaps_preserved = False

    if gaps_preserved:
        lines.extend([
            "### Gap Preservation: CONFIRMED",
            "",
            "All rotation methods preserve >= 95% of the original gap.",
            "This validates that rotation is indeed isometric for practical purposes.",
            "",
        ])
    else:
        lines.extend([
            "### Gap Preservation: PARTIAL",
            "",
            "Some rotation methods show gap degradation.",
            "This may indicate numerical issues or non-orthogonality in the transform.",
            "",
        ])

    lines.extend([
        "---",
        "",
        "*Report generated by sprint602_ivf_aligned.py*",
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
                'init_gap': m['init_gap'],
                'kmeans_iterations': m['kmeans_iterations'],
                'final_mse': m['final_mse'],
                'final_gap': m['final_gap'],
                'recall_nprobe_10': m['recall_at_k'].get(10, None),
                'gap_preserved_pct': m.get('gap_preserved_pct', None)
            })

    with open(csv_path, 'w', newline='') as f:
        if rows:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)


# =============================================================================
# 7. Main Entry Point
# =============================================================================

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Sprint 6.02: Data-Aligned Spherical Code Initialization"
    )
    parser.add_argument("--sanity-check", action="store_true",
                       help="Run sanity check only")
    parser.add_argument("--n-samples", type=int, default=50000,
                       help="Number of data points")
    parser.add_argument("--n-centroids", type=int, nargs="+", default=[64, 256],
                       help="Codebook sizes")
    parser.add_argument("--seeds", type=int, nargs="+", default=[601, 602, 603],
                       help="Random seeds")
    parser.add_argument("--out-dir", type=str, default="sprint602_ivf_aligned",
                       help="Output directory")

    args = parser.parse_args()

    if args.sanity_check:
        passed, _ = run_sanity_check()
        return

    # Full benchmark
    script_dir = Path(__file__).parent
    out_dir = script_dir / args.out_dir

    print("="*60)
    print("Sprint 6.02: Data-Aligned Spherical Code Initialization")
    print("="*60)

    # Run sanity check first
    print("\nStep 1: Sanity check (gap preservation)")
    passed, _ = run_sanity_check()

    if not passed:
        print("\nWARNING: Sanity check failed. Proceeding anyway but results may be suspect.")

    print("\nStep 2: Full benchmark")

    all_results = run_benchmark_suite(
        out_dir=out_dir / "results",
        n_samples=args.n_samples,
        seeds=args.seeds,
        n_centroids_list=args.n_centroids
    )

    # Save and analyze
    json_path = out_dir / "sprint602_results.json"
    with open(json_path, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved results: {json_path}")

    summary = aggregate_results(all_results)
    criteria = check_success_criteria(summary)

    summary_path = out_dir / "sprint602_summary.json"
    with open(summary_path, 'w') as f:
        json.dump({'summary': summary, 'criteria': criteria}, f, indent=2)

    csv_path = out_dir / "sprint602_results.csv"
    results_to_csv(all_results, csv_path)
    print(f"Saved CSV: {csv_path}")

    report_path = out_dir / "sprint602_report.md"
    generate_report(summary, criteria, report_path)
    print(f"Saved report: {report_path}")

    # Print summary
    print("\n" + "="*60)
    print("FINAL RESULTS")
    print("="*60)

    for N in sorted(criteria.keys()):
        print(f"\nN = {N}:")
        for method, c in criteria[N].items():
            method_short = method.replace('spherical_', '')
            status = "ALL PASS" if c['all_pass'] else "FAIL"
            print(f"  {method_short}: {status}")
            print(f"    Convergence: {c['criterion_1_convergence']['actual']}")
            print(f"    Gap: {c['criterion_2_gap']['actual']}")
            print(f"    MSE: {c['criterion_3_mse']['actual']}")

    print("\n" + "="*60)


if __name__ == "__main__":
    main()
