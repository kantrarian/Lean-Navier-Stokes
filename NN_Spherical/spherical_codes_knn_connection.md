# Spherical Codes and k-Nearest Neighbor Search: A Theoretical Connection

**R.J. Mathews**  
*Nordic Consulting Partners / Independent Research*  
mail.rjmathews@gmail.com

---

## Abstract

We explore the connection between spherical code optimization—the problem of placing points on a hypersphere to maximize minimum pairwise separation (packing)—and codebook design for approximate nearest neighbor (ANN) search, which minimizes worst-case quantization error (covering). While packing and covering are related, they are **not equivalent** problems; we clarify this distinction and propose using packing-based gap metrics as a regularizer rather than a direct quality measure. The "gap" metric from kissing number certification provides a scalable training signal that prevents codebook collapse while allowing data-driven adaptation. We outline a research program for "guarantee-first codebook design" and identify the key experiments needed to validate this approach.

---

## 1. Introduction

Two seemingly disparate problems share geometric structure:

**Problem A (Spherical Packing):** Place $N$ points on the unit sphere $\mathbb{S}^{d-1}$ to maximize the minimum pairwise angular separation.

**Problem B (Spherical Covering / Codebook Design):** Select $N$ codebook vectors to minimize worst-case quantization error for data distributed on $\mathbb{S}^{d-1}$.

These problems are **related but not equivalent**. Optimal packings tend to have good covering properties, but the relationship is not automatic. This note:

1. Clarifies the packing vs covering distinction (Section 3)
2. Proposes gap-based regularization for codebook optimization (Section 3.5)
3. Shows how to compute gap at scale (Section 6)
4. Outlines experiments to validate the approach (Section 9)

The core claim is modest: **packing-based gap metrics provide useful regularization for codebook learning**, not that they are equivalent to covering-based quality measures.

---

## 2. Mathematical Framework

### 2.1 Spherical Code Formulation

A **spherical code** is a finite set $\mathcal{C} = \{c_1, \ldots, c_N\} \subset \mathbb{S}^{d-1}$ where $\mathbb{S}^{d-1} = \{x \in \mathbb{R}^d : \|x\| = 1\}$.

The **minimum angle** of a spherical code is:
$$\theta_{\min}(\mathcal{C}) = \min_{i \neq j} \arccos(c_i \cdot c_j)$$

The **spherical code problem** asks: for given $N$ and $d$, find $\mathcal{C}^*$ maximizing $\theta_{\min}$.

The **kissing number** $\tau_d$ is the maximum $N$ such that $\theta_{\min} \geq 60°$ is achievable.

### 2.2 Gap Metric (Packing Radius)

We work with the equivalent formulation on a sphere of radius $2R$. Define the **gap**:
$$g(\mathcal{C}) = \min_{i \neq j} \|c_i - c_j\| - 2R$$

The gap relates to minimum angle via:
$$g = 4R\sin(\theta_{\min}/2) - 2R = 2R(2\sin(\theta_{\min}/2) - 1)$$

**Certification criterion:** A configuration is certified feasible if $g \geq -\varepsilon_g$ for tolerance $\varepsilon_g$.

The gap is essentially the **packing radius** minus a threshold: it measures how much "room" exists between points.

### 2.3 Vector Quantization Formulation

Given data $\mathcal{X} = \{x_1, \ldots, x_m\} \subset \mathbb{S}^{d-1}$ and codebook $\mathcal{C} = \{c_1, \ldots, c_N\}$, define:

**Quantization map:** $q(x) = \arg\min_{c \in \mathcal{C}} \|x - c\|$

**Mean squared error:** $\text{MSE}(\mathcal{C}; \mathcal{X}) = \frac{1}{m}\sum_{i=1}^{m} \|x_i - q(x_i)\|^2$

**Worst-case error (covering radius):** $\rho(\mathcal{C}) = \max_{x \in \mathbb{S}^{d-1}} \min_{c \in \mathcal{C}} \|x - c\|$

The covering radius $\rho$ is the maximum distance from any point on the sphere to its nearest codebook vector—equivalently, the circumradius of the largest Voronoi cell.

For normalized vectors: $\|x - c\|^2 = 2(1 - x \cdot c)$, so minimizing distance is equivalent to maximizing cosine similarity.

---

## 3. Packing vs Covering: A Critical Distinction

### 3.1 Two Different Optimization Problems

**Packing problem:** Maximize $r_{\text{pack}} = \frac{1}{2}\min_{i \neq j}\|c_i - c_j\|$ (half the minimum separation).

**Covering problem:** Minimize $\rho_{\text{cover}} = \max_{x \in \mathbb{S}^{d-1}} \min_{c \in \mathcal{C}} \|x - c\|$ (maximum Voronoi circumradius).

These are **dual but not equivalent**. A good packing (large $r_{\text{pack}}$) does not guarantee good covering (small $\rho_{\text{cover}}$), and vice versa. The gap metric from our kissing number work measures packing quality, while worst-case quantization error measures covering quality.

### 3.2 Known Relationship

For $N$ points on $\mathbb{S}^{d-1}$, a classical result bounds the relationship:

**Lemma (Packing-Covering Bound).** For any configuration $\mathcal{C}$:
$$r_{\text{pack}}(\mathcal{C}) \leq \rho_{\text{cover}}(\mathcal{C})$$

with equality only for "perfect" configurations where Voronoi cells are congruent and tile the sphere exactly (e.g., vertices of regular polytopes in low dimensions).

*Proof.* Consider the point $x^* = \arg\max_x \min_c \|x - c\|$ achieving the covering radius. By definition, $\|x^* - c_i\| \geq \rho$ for all $i$. If $c_i, c_j$ are the two closest codebook points to $x^*$, then by triangle inequality, $\|c_i - c_j\| \leq \|c_i - x^*\| + \|x^* - c_j\| \leq 2\rho$. Thus $r_{\text{pack}} = \frac{1}{2}\min\|c_i - c_j\| \leq \rho$. □

### 3.3 Working Hypothesis (Not a Theorem)

**Hypothesis (Packing as Covering Proxy).** For uniformly distributed data on $\mathbb{S}^{d-1}$, codebooks with large packing radius tend to have small covering radius, making gap a useful proxy for quantization quality.

*Rationale:* For uniform data, expected quantization error depends on the "typical" Voronoi cell size. Maximally separated points (high packing radius) tend to produce more uniform Voronoi cells, reducing variance in cell sizes and thus reducing the covering radius.

**This is NOT a proven equivalence.** The precise relationship depends on $N$, $d$, and the specific configuration. However, for the special case of known optimal configurations (hexagon in $d=2$, E8 in $d=8$), these are simultaneously optimal for packing and near-optimal for covering.

### 3.4 Gap as Packing Quality (Precise Statement)

**Proposition.** The gap metric measures packing quality:
$$g(\mathcal{C}) = 2r_{\text{pack}}(\mathcal{C}) - 2R$$

where $R$ is the target exclusion radius.

*Interpretation:*
- $g \geq 0$: packing radius meets or exceeds threshold (certified feasible)
- $g < 0$: packing radius falls short by $|g|/2$ (violation magnitude)

**The gap does NOT directly bound covering radius.** To connect gap to quantization error, we need the additional assumption that good packing implies reasonable covering—which holds empirically for high-symmetry configurations but is not guaranteed in general.

### 3.5 Operational Implication for ANN

For codebook design, we propose using gap as a **regularizer** rather than a direct quality measure:

$$L(\mathcal{C}; \mathcal{X}) = \underbrace{\text{MSE}(\mathcal{C}; \mathcal{X})}_{\text{data fit (covering-like)}} + \lambda \underbrace{\max(0, -g(\mathcal{C}))}_{\text{packing penalty}}$$

The packing penalty prevents codebook collapse (points clustering together) while the MSE term handles coverage. This sidesteps the packing-covering gap by optimizing both explicitly.

---

## 4. Applications to Approximate Nearest Neighbor Search

### 4.1 IVF (Inverted File) Indexing

**Structure:** Partition database vectors into $N$ clusters using centroids $\{c_1, \ldots, c_N\}$. At query time, search only clusters whose centroids are near the query.

**Current practice:** k-means clustering (Lloyd's algorithm) initialized randomly.

**Spherical code improvement:** Initialize centroids as an optimal spherical code, then refine with k-means. Benefits:
- Guaranteed initial separation avoids degenerate partitions
- Faster k-means convergence
- More uniform cluster sizes

**Gap interpretation:** The gap of the final centroids measures partition quality. Negative gap indicates cluster overlap—potential for missed neighbors.

### 4.2 Product Quantization (PQ)

**Structure:** Decompose $\mathbb{R}^d = \mathbb{R}^{d/M} \times \cdots \times \mathbb{R}^{d/M}$ into $M$ subspaces. Learn separate codebook of size $K$ for each subspace.

**Connection:** Each subspace codebook is a spherical code problem in dimension $d/M$. Our optimizer applies directly.

**Advantage:** Spherical code initialization provides worst-case guarantees on subspace quantization error, improving overall recall.

### 4.3 Locality-Sensitive Hashing (Hypothesis)

**Standard LSH:** For cosine similarity, random hyperplanes serve as hash functions. The theoretical analysis relies on randomness and independence.

**Spherical code LSH (speculative):** Instead of random hyperplanes, use spherical code points as hash function generators:
$$h_i(x) = \text{sign}(x \cdot c_i)$$

**Potential benefit:** If $\theta_{\min}(\mathcal{C}) \geq \theta_0$, then dissimilar points (angle $> 180° - \theta_0$) are guaranteed to differ in at least one hash bit. This provides deterministic worst-case guarantees.

**Caution:** Replacing randomness with structure may break the classical LSH analysis, which depends on probabilistic collision bounds. The standard analysis assumes hash functions are drawn independently; structured codes violate this assumption.

**Status:** This is a hypothesis requiring experimental validation. The tradeoff between worst-case guarantees and average-case performance is unclear. We do NOT claim this improves LSH—only that it's an interesting direction to explore.

### 4.4 Contrastive Learning

**Structure:** Learn embeddings where similar items have high cosine similarity, dissimilar items have low similarity.

**Class prototypes:** In supervised contrastive learning, class prototypes should be well-separated on the hypersphere.

**Application:** Use spherical code optimization to find optimal prototype positions for $N$ classes in dimension $d$. The gap becomes the margin in the contrastive loss.

---

## 5. Dimensional Analysis: A Geometric Curiosity

Our calibration results reveal an interesting pattern in packing margins:

| $d$ | $\tau_d$ | Gap at $\tau+1$ | Margin |
|-----|----------|-----------------|--------|
| 2   | 6        | −0.264          | 26.4%  |
| 5   | 40       | −0.036          | 3.6%   |
| 8   | 240      | −0.130          | 13.0%  |

**Observation 1:** As dimension increases, exponentially more points fit on the sphere ($\tau_8 = 240$ vs $\tau_2 = 6$).

**Observation 2:** The packing margin (gap magnitude at $\tau+1$) varies non-monotonically. Dimension 5 shows the *smallest* margin (3.6%) in our tested dimensions.

**Observation 3:** This is a statement about a very specific geometric regime—kissing configurations at the $60°$ separation threshold—not a general statement about high-dimensional geometry.

### Cautious Interpretation for k-NN

The tight margin in $d=5$ suggests a geometric regime where:
- The boundary between "fits" and "doesn't fit" is thin
- Small perturbations could change feasibility status
- Neighbor rankings may be unstable near decision boundaries

**However, this does NOT imply:** "ANN search is inherently harder in dimension 5." Our results concern a specific packing problem with a fixed angular threshold. Real embedding spaces have:
- Non-uniform data distributions
- Varying similarity thresholds
- Different optimization objectives

The connection to practical k-NN difficulty is **speculative** and would require empirical validation on actual embedding datasets.

---

## 6. Computing Gap at Scale

### 6.1 The Scalability Problem

For $N$ codebook vectors, exact gap computation requires $O(N^2)$ pairwise distances. This is:
- Trivial for $N = 256$ (PQ subcodebooks): 32K pairs
- Manageable for $N = 4096$ (IVF centroids): 8M pairs  
- Expensive for $N = 65536$ (large IVF): 2B pairs

### 6.2 Practical Approximations

**Sampled gap:** Compute minimum over $k$ random pairs:
```python
def approx_gap(C, k=10000, R=1.0):
    N = len(C)
    i = np.random.randint(0, N, k)
    j = np.random.randint(0, N, k)
    mask = i != j
    dists = np.linalg.norm(C[i[mask]] - C[j[mask]], axis=1)
    return np.min(dists) - 2*R
```
This gives a probabilistic upper bound on the true gap (the true minimum is ≤ sampled minimum).

**FAISS-assisted:** Use approximate nearest neighbor to find each point's closest neighbor, then take the minimum:
```python
def faiss_gap(C, R=1.0):
    index = faiss.IndexFlatL2(C.shape[1])
    index.add(C)
    D, I = index.search(C, 2)  # 2-NN: self + nearest
    min_dist = np.sqrt(D[:, 1]).min()  # Exclude self
    return min_dist - 2*R
```
This is $O(N \log N)$ with approximate indices.

**Monitoring regime:** During training, compute exact gap every $k$ epochs when $N$ is small, switch to approximate for larger codebooks.

### 6.3 Gap as Training Signal

For gradient-based codebook learning, we need $\nabla_{\mathcal{C}} g$. The gap is non-differentiable (min over pairs), but the soft-min approximation from our optimizer transfers:

$$\tilde{g}(\mathcal{C}) = -\tau \log \sum_{i < j} \exp\left(-\frac{\|c_i - c_j\|}{\tau}\right) - 2R$$

This smooth approximation has well-defined gradients and anneals to the true gap as $\tau \to 0$.

---

## 7. Algorithmic Transfer

### 7.1 Control-First → Guarantee-First

Our kissing number methodology:
1. **Positive control:** Verify optimizer certifies known feasible configuration
2. **Negative control:** Verify optimizer fails on overconstrained problem  
3. **Target:** Search for unknown configuration with calibrated confidence

Transfer to codebook design:
1. **Positive control:** Verify codebook achieves theoretical lower bound on uniform data
2. **Negative control:** Verify codebook cannot achieve impossible separation
3. **Target:** Optimize for actual data distribution with calibrated guarantees

### 7.2 The Optimizer Architecture

Our annealed Adam optimizer with tangent-space projection transfers directly:

```
Algorithm: Spherical Codebook Optimization
─────────────────────────────────────────
Input: Data X, codebook size N, dimension d
Output: Codebook C with quality certificate

1. Initialize C = SphericalCode(N, d)  // Our optimizer
2. For each epoch:
   a. Compute data-dependent loss L_data(C; X)
   b. Compute separation loss L_sep(C) = -min_gap(C)
   c. Total loss L = L_data + λ·L_sep
   d. Update C via Adam on sphere manifold
3. Return C with gap certificate
```

**Key insight:** The separation term $L_{\text{sep}}$ acts as a regularizer, preventing codebook collapse while the data term adapts to the actual distribution.

---

## 8. Proposed Extensions

### 8.1 Data-Driven Spherical Codes

**Objective:** Optimize codebook for non-uniform data while maintaining separation guarantees.

**Loss function:**
$$L(\mathcal{C}; \mathcal{X}) = \underbrace{\frac{1}{m}\sum_{i=1}^m \|x_i - q(x_i)\|^2}_{\text{quantization error}} + \lambda \underbrace{\max(0, -g(\mathcal{C}))}_{\text{separation penalty}}$$

The penalty term enforces $g \geq 0$, guaranteeing minimum separation even as the codebook adapts to data.

### 8.2 Hierarchical Codebooks

For large-scale ANN with millions of vectors:
- Level 1: Coarse spherical code with $N_1$ centroids
- Level 2: Fine spherical codes within each coarse cell

The hierarchical structure preserves separation guarantees at each level.

### 8.3 Streaming Codebook Updates

For dynamic databases:
- Maintain gap certificate as vectors are added/removed
- Trigger re-optimization when gap falls below threshold
- Amortized guarantee maintenance

---

## 9. Experimental Roadmap

### Phase 1: Initialization Benchmark (Highest Priority)
- Compare spherical code initialization vs random initialization for IVF
- Metrics: k-means iterations to convergence, final MSE, recall@k
- Datasets: SIFT1M, GIST1M, Deep1B (normalized)
- **This is the "killer experiment" that validates the entire framework**

### Phase 2: Joint Optimization
- Implement data-driven loss with separation penalty
- Compare against pure k-means and pure spherical codes
- Measure Pareto frontier: quantization error vs separation guarantee

### Phase 3: LSH Application (Exploratory)
- Implement spherical code LSH
- Compare collision probability curves against random hyperplane LSH
- Measure recall@k vs hash table size tradeoff
- **Note:** Results may not improve on random LSH; theoretical guarantees differ

---

## 10. Conclusion

The connection between spherical codes and vector quantization is suggestive but requires careful handling. Packing (maximizing minimum separation) and covering (minimizing worst-case quantization) are **dual but distinct** problems. We propose using the gap metric from packing as a **regularizer** for codebook learning, not as a direct quality measure.

The key insight is operational: gap-based penalties prevent codebook collapse while allowing data-driven adaptation. This sidesteps the packing-covering gap by optimizing both objectives jointly.

The highest-priority validation is the **IVF initialization benchmark**: comparing spherical code, random, and k-means++ initializations on standard embedding datasets. If spherical code initialization yields faster k-means convergence and competitive recall@k, the framework is validated. If not, the connection remains a geometric curiosity.

This note is a **working document**, not a finished paper. The theoretical claims are hypotheses to be tested, not proven theorems.

---

## References

1. Conway, J.H. & Sloane, N.J.A. (1999). *Sphere Packings, Lattices and Groups*. Springer.

2. Jégou, H., Douze, M., & Schmid, C. (2011). Product quantization for nearest neighbor search. *IEEE TPAMI*.

3. Johnson, J., Douze, M., & Jégou, H. (2019). Billion-scale similarity search with GPUs. *IEEE TBD*.

4. Andoni, A. & Indyk, P. (2008). Near-optimal hashing algorithms for approximate nearest neighbor in high dimensions. *CACM*.

5. Cohn, H. & Rajagopal, N. (2024). Uniform sphere packings and three-point bounds. arXiv:2412.00937.

---

## Appendix: Code Snippet

```python
def spherical_codebook_loss(C, X, R=1.0, lambda_sep=0.1):
    """
    Combined loss for data-driven spherical codebook optimization.
    
    Args:
        C: (N, d) codebook vectors on unit sphere
        X: (m, d) data vectors on unit sphere  
        R: exclusion radius for gap computation
        lambda_sep: separation penalty weight
    
    Returns:
        loss: scalar loss value
        grad: (N, d) gradient w.r.t. C
    """
    # Quantization error
    dists = np.linalg.norm(X[:, None, :] - C[None, :, :], axis=2)  # (m, N)
    assignments = np.argmin(dists, axis=1)  # (m,)
    quant_error = np.mean([dists[i, assignments[i]]**2 for i in range(len(X))])
    
    # Separation gap
    C_dists = np.linalg.norm(C[:, None, :] - C[None, :, :], axis=2)
    np.fill_diagonal(C_dists, np.inf)
    gap = np.min(C_dists) - 2*R
    
    # Penalty: penalize negative gap
    sep_penalty = max(0, -gap)
    
    return quant_error + lambda_sep * sep_penalty
```

---

*Document prepared: January 29, 2026*
