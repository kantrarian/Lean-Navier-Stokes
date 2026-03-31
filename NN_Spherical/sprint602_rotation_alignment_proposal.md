# Sprint 6.02: Data-Aligned Spherical Code Initialization
## Rotation Alignment to Fix the Migration Problem

**Author:** R.J. Mathews  
**Date:** 2026-01-30  
**Status:** Proposed  
**Prerequisite:** Sprint 6.01 (completed - hypothesis partially rejected)

---

## Motivation

Sprint 6.01 revealed that spherical code initialization takes **70-145% MORE iterations** than random, despite achieving similar final quality. The root cause:

> "Spherical codes maximize separation without considering where the data lies. Centroids must migrate from their initial positions to data clusters."

**Key Insight:** The spherical code has good *geometry* (separation) but bad *orientation* (misaligned with data).

**New Hypothesis:** Rotating the spherical code to align with the data distribution will:
1. Preserve separation guarantees (rotation is isometric)
2. Reduce migration distance (centroids start near data)
3. Achieve faster convergence than unrotated spherical code
4. Potentially beat random initialization

---

## Rotation Strategies

### Strategy A: PCA Alignment

Align spherical code principal axes with data principal axes.

```python
def align_pca(spherical_code: np.ndarray, data: np.ndarray) -> np.ndarray:
    """
    Rotate spherical code so its principal components align with data PCs.
    
    Rationale: Data variance directions should match codebook spread directions.
    """
    # Compute principal components
    data_centered = data - data.mean(axis=0)
    _, _, Vt_data = np.linalg.svd(data_centered, full_matrices=False)
    
    code_centered = spherical_code - spherical_code.mean(axis=0)
    _, _, Vt_code = np.linalg.svd(code_centered, full_matrices=False)
    
    # Rotation matrix: R @ Vt_code = Vt_data
    R = Vt_data.T @ Vt_code
    
    # Apply rotation
    rotated = spherical_code @ R.T
    
    # Re-normalize to unit sphere
    return rotated / np.linalg.norm(rotated, axis=1, keepdims=True)
```

**Complexity:** O(n·d²) for SVD on data, O(N·d²) for rotation. Negligible compared to spherical code generation.

### Strategy B: Procrustes Alignment

Find optimal rotation to minimize distance to k-means++ initialization.

```python
def align_procrustes(spherical_code: np.ndarray, target: np.ndarray) -> np.ndarray:
    """
    Orthogonal Procrustes: find rotation R minimizing ||spherical_code @ R - target||_F
    
    Rationale: k-means++ gives data-aware positions; align spherical code to them.
    """
    # Solve Procrustes: R = V @ U.T where target.T @ spherical_code = U @ S @ V.T
    M = target.T @ spherical_code
    U, _, Vt = np.linalg.svd(M)
    R = U @ Vt
    
    # Apply rotation
    rotated = spherical_code @ R.T
    return rotated / np.linalg.norm(rotated, axis=1, keepdims=True)
```

**Note:** This requires running k-means++ first, so total init cost = k-means++ + spherical code + alignment.

### Strategy C: Cluster Center Matching

Compute approximate cluster centers from data, then rotate spherical code to match.

```python
def align_to_clusters(spherical_code: np.ndarray, data: np.ndarray, 
                      n_sample: int = 10000) -> np.ndarray:
    """
    Quick clustering on data sample, then Procrustes align to cluster centers.
    
    Rationale: Get approximate data structure cheaply, align spherical code to it.
    """
    N = len(spherical_code)
    
    # Subsample for speed
    idx = np.random.choice(len(data), min(n_sample, len(data)), replace=False)
    sample = data[idx]
    
    # Quick k-means (few iterations, just to find rough centers)
    centers = sample[np.random.choice(len(sample), N, replace=False)]
    for _ in range(10):  # Just 10 iterations
        dists = np.linalg.norm(sample[:, None] - centers[None, :], axis=2)
        assignments = np.argmin(dists, axis=1)
        for i in range(N):
            mask = assignments == i
            if mask.sum() > 0:
                centers[i] = sample[mask].mean(axis=0)
        centers = centers / np.linalg.norm(centers, axis=1, keepdims=True)
    
    # Procrustes align spherical code to these rough centers
    return align_procrustes(spherical_code, centers)
```

**Complexity:** O(n_sample · N · d) for quick clustering + O(N · d²) for Procrustes.

### Strategy D: Moment Matching

Match first and second moments of spherical code to data.

```python
def align_moments(spherical_code: np.ndarray, data: np.ndarray) -> np.ndarray:
    """
    Affine transform spherical code to match data mean and covariance.
    
    Note: This is NOT a pure rotation - it's an affine map that may break
    the separation guarantees. Include for comparison but expect issues.
    """
    # Data statistics
    mu_data = data.mean(axis=0)
    cov_data = np.cov(data.T)
    
    # Spherical code statistics  
    mu_code = spherical_code.mean(axis=0)
    cov_code = np.cov(spherical_code.T)
    
    # Whitening + coloring transform
    # X_new = cov_data^{1/2} @ cov_code^{-1/2} @ (X - mu_code) + mu_data
    
    # ... (eigendecomposition for matrix square roots)
    
    # Re-normalize
    return transformed / np.linalg.norm(transformed, axis=1, keepdims=True)
```

**Caution:** Moment matching is NOT isometric. It may destroy separation properties. Test but expect degradation.

---

## Experiment Design

### Methods to Compare

| Method | Description | Preserves Separation? |
|--------|-------------|----------------------|
| Random | Baseline | N/A |
| k-means++ | Data-aware baseline | N/A |
| Spherical (unrotated) | Sprint 6.01 result | Yes |
| Spherical + PCA | Align to data PCs | Yes |
| Spherical + Procrustes | Align to k-means++ | Yes |
| Spherical + ClusterMatch | Align to quick clusters | Yes |

### Metrics

Same as Sprint 6.01:
1. **Convergence:** k-means iterations to tolerance
2. **Final MSE:** Quantization error
3. **Final Gap:** Packing quality (did rotation preserve it?)
4. **Recall@10:** Search quality
5. **Init Time:** Including rotation cost

### Success Criteria

| Criterion | Target |
|-----------|--------|
| Convergence | Spherical+Rotation achieves ≥20% fewer iterations than unrotated |
| Gap Preservation | Spherical+Rotation gap ≥ 95% of unrotated gap |
| Final MSE | Within 5% of k-means++ |

---

## Hypotheses

**H1 (Primary):** PCA-aligned spherical codes converge faster than unrotated spherical codes.

**H2 (Ambitious):** PCA-aligned spherical codes converge faster than random initialization.

**H3 (Separation):** Rotation preserves gap (isometry property).

**H4 (Quality):** Final MSE and recall remain competitive.

---

## Implementation

```python
def init_spherical_aligned(N: int, dim: int, data: np.ndarray, 
                           method: str = 'pca', seed: int = 42) -> np.ndarray:
    """
    Generate spherical code and align to data.
    
    Args:
        N: Number of centroids
        dim: Dimension
        data: Data matrix (n_samples, dim) on unit sphere
        method: 'pca', 'procrustes', 'cluster'
        seed: Random seed
    
    Returns:
        Aligned centroids (N, dim) on unit sphere
    """
    # Generate spherical code (from sprint520)
    spherical = init_spherical_code(N, dim, seed)
    
    # Align
    if method == 'pca':
        return align_pca(spherical, data)
    elif method == 'procrustes':
        target = init_kmeans_pp(data, N, seed)
        return align_procrustes(spherical, target)
    elif method == 'cluster':
        return align_to_clusters(spherical, data)
    else:
        return spherical  # Unrotated
```

---

## Expected Outcomes

### If H1 is SUPPORTED:
- Rotation fixes the migration problem
- Spherical codes become viable for IVF initialization
- PCA alignment is cheap and effective

### If H1 is REJECTED:
- The problem is not just orientation but fundamental mismatch between packing objective and clustering objective
- Data-aware methods (k-means++) are inherently better for initialization
- Spherical codes are only useful as regularizers during training, not initializers

### Key Insight Either Way:
The experiment will clarify whether the Sprint 6.01 failure was due to:
- **Orientation** (fixable with rotation) → H1 supported
- **Objective mismatch** (packing ≠ clustering) → H1 rejected

---

## Prompt for Execution

```
You have access to:
- sprint601_ivf_benchmark.py (baseline benchmark from Sprint 6.01)
- sprint520_bookend_controls.py (spherical code optimizer)

Execute Sprint 6.02: Data-Aligned Spherical Code Initialization

TASK: Extend Sprint 6.01 to test rotation alignment strategies.

NEW METHODS TO ADD:
1. Spherical + PCA alignment
2. Spherical + Procrustes alignment (to k-means++ positions)  
3. Spherical + Quick cluster matching

REUSE from Sprint 6.01:
- Data generation
- k-means refinement
- Recall evaluation
- Reporting infrastructure

KEY QUESTION: Does alignment fix the convergence problem?

SUCCESS CRITERIA:
- Aligned spherical code converges ≥20% faster than unrotated
- Gap preserved ≥95% after rotation
- Final MSE within 5% of k-means++

Run on same configuration as Sprint 6.01:
- 50,000 samples, dim=128, N={64, 256}
- Seeds: 601, 602, 603

DELIVERABLES:
1. sprint602_ivf_aligned.py
2. sprint602_results.csv  
3. sprint602_report.md with verdict on rotation hypothesis
```

---

## Quick Test First

Before full experiment, sanity check with N=64, 1 seed:

```python
# Quick validation
data = generate_normalized_data(10000, 128, 50, 0.3, seed=42)

# Unrotated
spherical = init_spherical_code(64, 128, seed=42)
gap_before = compute_gap(spherical)

# PCA aligned  
aligned = align_pca(spherical, data)
gap_after = compute_gap(aligned)

print(f"Gap before: {gap_before:.4f}")
print(f"Gap after:  {gap_after:.4f}")
print(f"Preserved:  {gap_after/gap_before*100:.1f}%")

# If gap is NOT preserved (< 95%), rotation is problematic
# If gap IS preserved, proceed with full experiment
```

---

## Timeline

| Phase | Duration | Notes |
|-------|----------|-------|
| Implement alignment functions | 30 min | PCA, Procrustes, ClusterMatch |
| Sanity check gap preservation | 15 min | Critical - if gap breaks, stop |
| Full benchmark | 2-3 hours | Reuse Sprint 6.01 infrastructure |
| Analysis | 30 min | Compare to Sprint 6.01 results |

---

*Sprint proposed: 2026-01-30*
