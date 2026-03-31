# Sprint 6.01: IVF Initialization Benchmark
## Spherical Code vs Random vs k-means++ for Codebook Initialization

**Author:** R.J. Mathews  
**Date:** 2026-01-29  
**Status:** Ready for Execution

---

## Executive Summary

This sprint tests the hypothesis that **spherical code initialization** improves IVF (Inverted File) codebook quality compared to random and k-means++ initialization. This is the "killer experiment" for validating the theoretical connection between spherical packing and vector quantization.

**Hypothesis:** Codebooks initialized with maximally-separated spherical codes will:
1. Converge faster during k-means refinement (fewer iterations)
2. Achieve lower final quantization error (MSE)
3. Maintain competitive recall@k for nearest neighbor search

**Null hypothesis to reject:** Spherical code initialization performs no better than random initialization.

---

## Background

The file `sprint520_bookend_controls.py` contains a spherical code optimizer that:
- Maximizes minimum pairwise separation on the unit sphere
- Uses annealed Adam with tangent-space projection
- Certifies configurations via gap metric: g = min_dist - threshold

The file `spherical_codes_knn_connection.md` establishes that:
- Packing (max separation) ≠ Covering (min quantization error)
- But good packings tend to produce good coverings empirically
- Gap-based regularization prevents codebook collapse

**This sprint provides empirical validation.**

---

## Experiment Design

### Dataset

Use **synthetic normalized embeddings** for controlled evaluation:

```python
def generate_normalized_data(n_samples: int, dim: int, n_clusters: int, 
                              cluster_std: float, seed: int) -> np.ndarray:
    """
    Generate clustered data on unit sphere.
    
    This simulates real embedding distributions which are:
    - High-dimensional
    - Approximately normalized (cosine similarity)
    - Clustered (semantic structure)
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
```

**Parameters:**
- `n_samples`: 100,000 (manageable but statistically meaningful)
- `dim`: 128 (typical embedding dimension)
- `n_clusters`: 100 (ground truth structure)
- `cluster_std`: 0.3 (moderate spread)
- `seed`: 601 (reproducibility)

### Codebook Sizes to Test

| N_centroids | Regime | Rationale |
|-------------|--------|-----------|
| 64 | Small | PQ subcodebook scale |
| 256 | Medium | Typical IVF |
| 1024 | Large | Stress test |

### Initialization Methods

**Method A: Random**
```python
def init_random(N: int, dim: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    centroids = rng.normal(size=(N, dim))
    return (centroids / np.linalg.norm(centroids, axis=1, keepdims=True)).astype(np.float32)
```

**Method B: k-means++**
```python
def init_kmeans_pp(data: np.ndarray, N: int, seed: int) -> np.ndarray:
    """Standard k-means++ initialization."""
    rng = np.random.default_rng(seed)
    n_samples, dim = data.shape
    
    centroids = [data[rng.integers(n_samples)]]
    
    for _ in range(N - 1):
        # Compute distances to nearest centroid
        dists = np.min([np.linalg.norm(data - c, axis=1)**2 for c in centroids], axis=0)
        probs = dists / dists.sum()
        idx = rng.choice(n_samples, p=probs)
        centroids.append(data[idx])
    
    return np.array(centroids, dtype=np.float32)
```

**Method C: Spherical Code**
```python
def init_spherical_code(N: int, dim: int, seed: int, 
                        restarts: int = 10, iters: int = 5000) -> np.ndarray:
    """
    Initialize using spherical code optimizer from sprint520.
    Maximize minimum pairwise separation.
    """
    from sprint520_bookend_controls import (
        project_all, logsumexp_maxmin_and_grad, 
        project_grad_tangent, AdamState, min_gap
    )
    
    rng = np.random.default_rng(seed)
    best_centroids = None
    best_gap = -np.inf
    
    for r in range(restarts):
        # Random init on unit sphere
        x = rng.normal(size=(N, dim))
        x = project_all(x, 1.0)
        
        adam = AdamState((N, dim))
        tau = 0.1  # Logsumexp temperature
        
        for i in range(iters):
            # Anneal temperature
            tau_t = max(0.01, tau * (0.9999 ** i))
            
            # Gradient step to maximize min distance
            loss, grad = logsumexp_maxmin_and_grad(x, R=0.5, tau=tau_t)
            grad = project_grad_tangent(x, grad)
            step = adam.step(grad, lr=0.01)
            x = x - step
            x = project_all(x, 1.0)
        
        gap = min_gap(x, R=0.5)
        if gap > best_gap:
            best_gap = gap
            best_centroids = x.copy()
    
    return best_centroids.astype(np.float32)
```

### k-means Refinement

All initializations refined with identical k-means:

```python
def run_kmeans(data: np.ndarray, init_centroids: np.ndarray, 
               max_iters: int = 100, tol: float = 1e-6) -> dict:
    """
    Run k-means from given initialization.
    Track convergence and final quality.
    """
    centroids = init_centroids.copy()
    N, dim = centroids.shape
    n_samples = len(data)
    
    history = {
        'mse': [],
        'delta': [],
        'gap': []
    }
    
    for iteration in range(max_iters):
        # Assignment step
        dists = np.linalg.norm(data[:, None, :] - centroids[None, :, :], axis=2)
        assignments = np.argmin(dists, axis=1)
        
        # Compute MSE
        mse = np.mean([dists[i, assignments[i]]**2 for i in range(n_samples)])
        history['mse'].append(mse)
        
        # Compute gap (packing quality)
        centroid_dists = np.linalg.norm(centroids[:, None, :] - centroids[None, :, :], axis=2)
        np.fill_diagonal(centroid_dists, np.inf)
        gap = np.min(centroid_dists)
        history['gap'].append(gap)
        
        # Update step
        new_centroids = np.zeros_like(centroids)
        counts = np.zeros(N)
        for i, a in enumerate(assignments):
            new_centroids[a] += data[i]
            counts[a] += 1
        
        # Handle empty clusters
        empty = counts == 0
        if np.any(empty):
            # Reinitialize empty clusters to random data points
            empty_idx = np.where(empty)[0]
            for idx in empty_idx:
                new_centroids[idx] = data[np.random.randint(n_samples)]
                counts[idx] = 1
        
        new_centroids = new_centroids / counts[:, None]
        
        # Normalize to sphere
        new_centroids = new_centroids / np.linalg.norm(new_centroids, axis=1, keepdims=True)
        
        # Check convergence
        delta = np.max(np.linalg.norm(new_centroids - centroids, axis=1))
        history['delta'].append(delta)
        
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
```

### Recall@k Evaluation

```python
def compute_recall_at_k(data: np.ndarray, centroids: np.ndarray, 
                        queries: np.ndarray, k: int = 10, n_probe: int = 10) -> float:
    """
    Compute recall@k using IVF-style search.
    
    1. Find n_probe nearest centroids to query
    2. Search only vectors assigned to those centroids
    3. Compare to ground truth k-NN
    """
    # Build inverted index
    dists_to_centroids = np.linalg.norm(data[:, None, :] - centroids[None, :, :], axis=2)
    assignments = np.argmin(dists_to_centroids, axis=1)
    
    inverted_lists = {i: [] for i in range(len(centroids))}
    for idx, a in enumerate(assignments):
        inverted_lists[a].append(idx)
    
    # Ground truth: brute force k-NN
    query_dists = np.linalg.norm(queries[:, None, :] - data[None, :, :], axis=2)
    ground_truth = np.argsort(query_dists, axis=1)[:, :k]
    
    # IVF search
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
        candidate_data = data[candidates]
        candidate_dists = np.linalg.norm(candidate_data - query, axis=1)
        top_k_local = np.argsort(candidate_dists)[:k]
        retrieved = set([candidates[i] for i in top_k_local])
        
        # Compute recall
        true_set = set(ground_truth[q_idx])
        recall = len(retrieved & true_set) / k
        recalls.append(recall)
    
    return np.mean(recalls)
```

---

## Metrics & Success Criteria

### Primary Metrics

| Metric | Definition | Success if Spherical Code... |
|--------|------------|------------------------------|
| **Convergence Speed** | Iterations to δ < 10⁻⁶ | ≥20% fewer iterations than Random |
| **Final MSE** | Mean squared quantization error | ≤ 5% worse than k-means++ |
| **Final Gap** | Min pairwise centroid distance | ≥ 10% better than alternatives |
| **Recall@10** | IVF search accuracy (n_probe=10) | Within 2% of k-means++ |

### Secondary Metrics

- Recall@10 at n_probe = {1, 5, 10, 20} (probe curve)
- Empty cluster count during k-means
- MSE trajectory (convergence curve)

### Statistical Requirements

- **5 random seeds** per configuration
- Report mean ± std
- Wilcoxon signed-rank test for pairwise comparisons (p < 0.05)

---

## Output Specification

### Directory Structure

```
sprint601_ivf_benchmark/
├── config.json              # Experiment configuration
├── results/
│   ├── N64_seed601.json     # Per-run results
│   ├── N64_seed602.json
│   └── ...
├── figures/
│   ├── convergence_N256.png # MSE vs iteration curves
│   ├── recall_curve.png     # Recall@k vs n_probe
│   └── summary_table.png    # Main results table
├── sprint601_report.md      # Auto-generated report
└── sprint601_results.csv    # Machine-readable summary
```

### JSON Result Schema

```json
{
  "config": {
    "N_centroids": 256,
    "dim": 128,
    "n_samples": 100000,
    "seed": 601
  },
  "methods": {
    "random": {
      "init_time_sec": 0.01,
      "kmeans_iterations": 45,
      "final_mse": 0.0823,
      "final_gap": 0.312,
      "recall_at_10": {"nprobe_1": 0.32, "nprobe_5": 0.71, "nprobe_10": 0.85}
    },
    "kmeans_pp": {
      "init_time_sec": 2.34,
      "kmeans_iterations": 28,
      "final_mse": 0.0756,
      "final_gap": 0.298,
      "recall_at_10": {"nprobe_1": 0.35, "nprobe_5": 0.74, "nprobe_10": 0.87}
    },
    "spherical_code": {
      "init_time_sec": 45.2,
      "kmeans_iterations": 22,
      "final_mse": 0.0789,
      "final_gap": 0.387,
      "recall_at_10": {"nprobe_1": 0.34, "nprobe_5": 0.73, "nprobe_10": 0.86}
    }
  }
}
```

---

## Implementation Checklist

```
[ ] 1. Data generation
    [ ] generate_normalized_data() implemented and tested
    [ ] Verify clustering structure visually (PCA projection)

[ ] 2. Initialization methods
    [ ] init_random() - trivial
    [ ] init_kmeans_pp() - standard algorithm
    [ ] init_spherical_code() - integrate sprint520 optimizer

[ ] 3. k-means refinement
    [ ] run_kmeans() with history tracking
    [ ] Handle empty clusters gracefully
    [ ] Verify convergence on simple case

[ ] 4. Evaluation
    [ ] compute_recall_at_k() with IVF simulation
    [ ] Ground truth brute-force verification

[ ] 5. Experiment loop
    [ ] 3 codebook sizes × 3 methods × 5 seeds = 45 runs
    [ ] Progress logging
    [ ] Checkpoint intermediate results

[ ] 6. Analysis & reporting
    [ ] Aggregate statistics (mean ± std)
    [ ] Generate convergence plots
    [ ] Generate recall curves
    [ ] Statistical significance tests
    [ ] Auto-generate markdown report
```

---

## Prompt for Claude Code Execution

```
You have access to:
- sprint520_bookend_controls.py (spherical code optimizer)
- spherical_codes_knn_connection.md (theoretical background)

Execute Sprint 6.01: IVF Initialization Benchmark

TASK: Implement and run the experiment comparing spherical code vs random vs k-means++ 
initialization for IVF codebooks.

CONSTRAINTS:
- Use only NumPy (no FAISS dependency for this benchmark)
- Synthetic data only (no external datasets)
- All code must be self-contained and reproducible

DELIVERABLES:
1. sprint601_ivf_benchmark.py - Complete benchmark script
2. sprint601_results.csv - Aggregated results
3. sprint601_report.md - Analysis with plots (as ASCII tables if no matplotlib)

SUCCESS CRITERIA (from spec):
- Spherical code achieves ≥20% fewer k-means iterations than random
- Spherical code MSE within 5% of k-means++
- Spherical code recall@10 within 2% of k-means++

If ANY criterion fails, report honestly - this is hypothesis testing, not advocacy.

START by reading the sprint520 optimizer code to understand the spherical code 
generation, then implement the benchmark pipeline incrementally:
1. Data generation (test with small N first)
2. Each initialization method (verify independently)
3. k-means refinement (check convergence)
4. Full experiment loop
5. Analysis and reporting

Be rigorous. This experiment validates or invalidates a theoretical framework.
```

---

## Expected Outcomes

### If Hypothesis is SUPPORTED:
- Spherical codes converge faster (better initial separation → fewer reassignments)
- Final MSE is competitive (good packing ≈ good covering for uniform-ish data)
- Recall is maintained (centroid quality transfers to search quality)

**Implication:** Spherical code initialization is a viable technique for IVF systems. Worth testing on real datasets (SIFT1M, Deep1B).

### If Hypothesis is REJECTED:
- Spherical codes don't improve convergence (separation doesn't help k-means)
- OR final MSE is significantly worse (packing ≠ covering for this regime)
- OR recall degrades (centroid positions don't help search)

**Implication:** The packing→covering connection is weaker than hoped. Gap regularization may still be useful during training, but initialization is not the killer app.

### Either outcome is scientifically valuable.

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| Implementation | 2-3 hours | Working benchmark script |
| Small-scale test | 30 min | Verify correctness on N=64 |
| Full benchmark | 1-2 hours | All 45 runs complete |
| Analysis | 30 min | Report and figures |

**Total: ~4-5 hours of compute time**

---

## Notes for Execution

1. **Start small:** Test with N=64, n_samples=10000, 1 seed before scaling up.

2. **The spherical code init is slow:** Budget 30-60 sec per codebook for N=256. This is acceptable for initialization (one-time cost) but note it in results.

3. **Watch for degenerate cases:** If spherical code optimization fails (gap << 0), fall back to random. Log these failures.

4. **Normalization matters:** Ensure all data and centroids stay on unit sphere throughout.

5. **Be honest:** If results don't support the hypothesis, say so clearly. Negative results are still results.

---

*Sprint prepared: 2026-01-29*
*Ready for execution*
