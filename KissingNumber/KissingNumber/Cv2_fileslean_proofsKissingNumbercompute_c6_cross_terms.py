"""
Compute C6*C6 cross-terms symbolically.

C6(x, (a,b,c,d,e,f)) = sum of 15 terms, each of form:
  x_i * x_j * (delta_kl * delta_mn + delta_km * delta_ln + delta_kn * delta_lm)
where {i,j,k,l,m,n} = {a,b,c,d,e,f}

C6a: first 5 terms (where 'a' is one of the free indices)
C6b: last 10 terms (where 'a' is not a free index)

We need to compute sum over all (a,b,c,d,e,f) in {0..7}^6 of C6a(x,p)*C6a(y,p) etc.
and express the result in terms of s = sum_i x_i*y_i, ||x||^2=1, ||y||^2=1.

For symbolic computation, we use the fact that after summing over all indices
with delta elimination, the result is a polynomial in:
  s^2 = (sum x_i*y_i)^2
  ||x||^2 = sum x_i^2 = 1
  ||y||^2 = sum y_i^2 = 1

So the answer has the form: alpha * s^2 + beta
where alpha and beta are integers we need to determine.

To find alpha and beta, we evaluate at two specific x,y pairs on the unit sphere in R^8:
1) x = y = e1 (first standard basis vector): s=1, so answer = alpha + beta
2) x = e1, y = e2 (orthogonal unit vectors): s=0, so answer = beta

Then alpha = answer(1) - answer(2), beta = answer(2).
"""
import numpy as np
from itertools import product as iproduct

N = 8  # dimension

def delta(i, j):
    return 1.0 if i == j else 0.0

def C6a_term(x, a, b, c, d, e, f):
    """C6a has 5 terms where 'a' is one of the two free indices."""
    return (
        x[a]*x[b]*(delta(c,d)*delta(e,f) + delta(c,e)*delta(d,f) + delta(c,f)*delta(d,e))
      + x[a]*x[c]*(delta(b,d)*delta(e,f) + delta(b,e)*delta(d,f) + delta(b,f)*delta(d,e))
      + x[a]*x[d]*(delta(b,c)*delta(e,f) + delta(b,e)*delta(c,f) + delta(b,f)*delta(c,e))
      + x[a]*x[e]*(delta(b,c)*delta(d,f) + delta(b,d)*delta(c,f) + delta(b,f)*delta(c,d))
      + x[a]*x[f]*(delta(b,c)*delta(d,e) + delta(b,d)*delta(c,e) + delta(b,e)*delta(c,d))
    )

def C6b_term(x, a, b, c, d, e, f):
    """C6b has 10 terms where 'a' is NOT a free index."""
    return (
        x[b]*x[c]*(delta(a,d)*delta(e,f) + delta(a,e)*delta(d,f) + delta(a,f)*delta(d,e))
      + x[b]*x[d]*(delta(a,c)*delta(e,f) + delta(a,e)*delta(c,f) + delta(a,f)*delta(c,e))
      + x[b]*x[e]*(delta(a,c)*delta(d,f) + delta(a,d)*delta(c,f) + delta(a,f)*delta(c,d))
      + x[b]*x[f]*(delta(a,c)*delta(d,e) + delta(a,d)*delta(c,e) + delta(a,e)*delta(c,d))
      + x[c]*x[d]*(delta(a,b)*delta(e,f) + delta(a,e)*delta(b,f) + delta(a,f)*delta(b,e))
      + x[c]*x[e]*(delta(a,b)*delta(d,f) + delta(a,d)*delta(b,f) + delta(a,f)*delta(b,d))
      + x[c]*x[f]*(delta(a,b)*delta(d,e) + delta(a,d)*delta(b,e) + delta(a,e)*delta(b,d))
      + x[d]*x[e]*(delta(a,b)*delta(c,f) + delta(a,c)*delta(b,f) + delta(a,f)*delta(b,c))
      + x[d]*x[f]*(delta(a,b)*delta(c,e) + delta(a,c)*delta(b,e) + delta(a,e)*delta(b,c))
      + x[e]*x[f]*(delta(a,b)*delta(c,d) + delta(a,c)*delta(b,d) + delta(a,d)*delta(b,c))
    )

def compute_sum(x, y, fx, fy):
    """Compute sum over all (a,b,c,d,e,f) in {0..7}^6 of fx(x,(a,b,c,d,e,f)) * fy(y,(a,b,c,d,e,f))"""
    total = 0.0
    for a in range(N):
        for b in range(N):
            for c in range(N):
                for d in range(N):
                    for e_idx in range(N):
                        for f_idx in range(N):
                            total += fx(x, a, b, c, d, e_idx, f_idx) * fy(y, a, b, c, d, e_idx, f_idx)
    return total

# Standard basis vectors
e1 = np.zeros(N); e1[0] = 1.0
e2 = np.zeros(N); e2[1] = 1.0

# Evaluate at (x=e1, y=e1): s=1
# and (x=e1, y=e2): s=0
print("Computing C6a*C6a...")
aa_s1 = compute_sum(e1, e1, C6a_term, C6a_term)  # s=1
aa_s0 = compute_sum(e1, e2, C6a_term, C6a_term)  # s=0
print(f"  C6a*C6a at s=1: {aa_s1}")
print(f"  C6a*C6a at s=0: {aa_s0}")
print(f"  => coeff of s^2 = {aa_s1 - aa_s0}, constant = {aa_s0}")
print(f"  => {int(aa_s1 - aa_s0)} * s^2 + {int(aa_s0)}")

print("\nComputing C6a*C6b...")
ab_s1 = compute_sum(e1, e1, C6a_term, C6b_term)
ab_s0 = compute_sum(e1, e2, C6a_term, C6b_term)
print(f"  C6a*C6b at s=1: {ab_s1}")
print(f"  C6a*C6b at s=0: {ab_s0}")
print(f"  => {int(ab_s1 - ab_s0)} * s^2 + {int(ab_s0)}")

print("\nComputing C6b*C6a...")
ba_s1 = compute_sum(e1, e1, C6b_term, C6a_term)
ba_s0 = compute_sum(e1, e2, C6b_term, C6a_term)
print(f"  C6b*C6a at s=1: {ba_s1}")
print(f"  C6b*C6a at s=0: {ba_s0}")
print(f"  => {int(ba_s1 - ba_s0)} * s^2 + {int(ba_s0)}")

print("\nComputing C6b*C6b...")
bb_s1 = compute_sum(e1, e1, C6b_term, C6b_term)
bb_s0 = compute_sum(e1, e2, C6b_term, C6b_term)
print(f"  C6b*C6b at s=1: {bb_s1}")
print(f"  C6b*C6b at s=0: {bb_s0}")
print(f"  => {int(bb_s1 - bb_s0)} * s^2 + {int(bb_s0)}")

total_s2 = int((aa_s1-aa_s0) + (ab_s1-ab_s0) + (ba_s1-ba_s0) + (bb_s1-bb_s0))
total_const = int(aa_s0 + ab_s0 + ba_s0 + bb_s0)
print(f"\nTotal C6*C6 = {total_s2} * s^2 + {total_const}")
print(f"Expected: 7560 * s^2 + 1080")
print(f"Match: {total_s2 == 7560 and total_const == 1080}")
