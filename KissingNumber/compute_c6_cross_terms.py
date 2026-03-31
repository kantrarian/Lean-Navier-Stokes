import numpy as np

N = 8

def delta(i, j):
    return 1.0 if i == j else 0.0

# C6a terms individually
def C6a_terms():
    """Return list of 5 term functions for C6a."""
    def term0(x, a, b, c, d, e, f):
        return x[a]*x[b]*(delta(c,d)*delta(e,f) + delta(c,e)*delta(d,f) + delta(c,f)*delta(d,e))
    def term1(x, a, b, c, d, e, f):
        return x[a]*x[c]*(delta(b,d)*delta(e,f) + delta(b,e)*delta(d,f) + delta(b,f)*delta(d,e))
    def term2(x, a, b, c, d, e, f):
        return x[a]*x[d]*(delta(b,c)*delta(e,f) + delta(b,e)*delta(c,f) + delta(b,f)*delta(c,e))
    def term3(x, a, b, c, d, e, f):
        return x[a]*x[e]*(delta(b,c)*delta(d,f) + delta(b,d)*delta(c,f) + delta(b,f)*delta(c,d))
    def term4(x, a, b, c, d, e, f):
        return x[a]*x[f]*(delta(b,c)*delta(d,e) + delta(b,d)*delta(c,e) + delta(b,e)*delta(c,d))
    return [term0, term1, term2, term3, term4]

# C6b terms individually
def C6b_terms():
    """Return list of 10 term functions for C6b."""
    def term0(x, a, b, c, d, e, f):
        return x[b]*x[c]*(delta(a,d)*delta(e,f) + delta(a,e)*delta(d,f) + delta(a,f)*delta(d,e))
    def term1(x, a, b, c, d, e, f):
        return x[b]*x[d]*(delta(a,c)*delta(e,f) + delta(a,e)*delta(c,f) + delta(a,f)*delta(c,e))
    def term2(x, a, b, c, d, e, f):
        return x[b]*x[e]*(delta(a,c)*delta(d,f) + delta(a,d)*delta(c,f) + delta(a,f)*delta(c,d))
    def term3(x, a, b, c, d, e, f):
        return x[b]*x[f]*(delta(a,c)*delta(d,e) + delta(a,d)*delta(c,e) + delta(a,e)*delta(c,d))
    def term4(x, a, b, c, d, e, f):
        return x[c]*x[d]*(delta(a,b)*delta(e,f) + delta(a,e)*delta(b,f) + delta(a,f)*delta(b,e))
    def term5(x, a, b, c, d, e, f):
        return x[c]*x[e]*(delta(a,b)*delta(d,f) + delta(a,d)*delta(b,f) + delta(a,f)*delta(b,d))
    def term6(x, a, b, c, d, e, f):
        return x[c]*x[f]*(delta(a,b)*delta(d,e) + delta(a,d)*delta(b,e) + delta(a,e)*delta(b,d))
    def term7(x, a, b, c, d, e, f):
        return x[d]*x[e]*(delta(a,b)*delta(c,f) + delta(a,c)*delta(b,f) + delta(a,f)*delta(b,c))
    def term8(x, a, b, c, d, e, f):
        return x[d]*x[f]*(delta(a,b)*delta(c,e) + delta(a,c)*delta(b,e) + delta(a,e)*delta(b,c))
    def term9(x, a, b, c, d, e, f):
        return x[e]*x[f]*(delta(a,b)*delta(c,d) + delta(a,c)*delta(b,d) + delta(a,d)*delta(b,c))
    return [term0, term1, term2, term3, term4, term5, term6, term7, term8, term9]

def make_group_fn(terms, indices):
    """Make a function that sums the given term indices."""
    selected = [terms[i] for i in indices]
    def fn(x, a, b, c, d, e, f):
        return sum(t(x, a, b, c, d, e, f) for t in selected)
    return fn

def compute_sum(x, y, fx, fy):
    total = 0.0
    for a in range(N):
        for b in range(N):
            for c in range(N):
                for d in range(N):
                    for e in range(N):
                        for f in range(N):
                            total += fx(x, a, b, c, d, e, f) * fy(y, a, b, c, d, e, f)
    return total

e1 = np.zeros(N); e1[0] = 1.0
e2 = np.zeros(N); e2[1] = 1.0

# Define groups
c6a = C6a_terms()
c6b = C6b_terms()

groups = {
    'C6a1': make_group_fn(c6a, [0, 1]),
    'C6a2': make_group_fn(c6a, [2, 3, 4]),
    'C6b1': make_group_fn(c6b, [0, 1, 2]),
    'C6b2': make_group_fn(c6b, [3, 4, 5]),
    'C6b3': make_group_fn(c6b, [6, 7, 8, 9]),
}

# Compute all unique cross-terms
pairs = [
    ('C6a1', 'C6a1'), ('C6a1', 'C6a2'), ('C6a2', 'C6a2'),
    ('C6a1', 'C6b1'), ('C6a1', 'C6b2'), ('C6a1', 'C6b3'),
    ('C6a2', 'C6b1'), ('C6a2', 'C6b2'), ('C6a2', 'C6b3'),
    ('C6b1', 'C6b1'), ('C6b1', 'C6b2'), ('C6b1', 'C6b3'),
    ('C6b2', 'C6b2'), ('C6b2', 'C6b3'),
    ('C6b3', 'C6b3'),
]

print("Cross-term results:")
print("=" * 60)
results = {}
for (name_x, name_y) in pairs:
    fx = groups[name_x]
    fy = groups[name_y]
    val_s1 = compute_sum(e1, e1, fx, fy)
    val_s0 = compute_sum(e1, e2, fx, fy)
    alpha = int(round(val_s1 - val_s0))
    beta = int(round(val_s0))
    results[(name_x, name_y)] = (alpha, beta)
    label = f"{name_x}*{name_y}"
    if beta != 0:
        rhs = f"{alpha} * s^2 + {beta}"
    else:
        rhs = f"{alpha} * s^2"
    print(f"  {label:16s} = {rhs}")

# Symmetry verification
print("\nSymmetry verification (should all be 0):")
print("=" * 60)
sym_ok = True
for (name_x, name_y) in pairs:
    fx = groups[name_x]
    fy = groups[name_y]
    val_xy_s1 = compute_sum(e1, e1, fx, fy)
    val_yx_s1 = compute_sum(e1, e1, fy, fx)
    val_xy_s0 = compute_sum(e1, e2, fx, fy)
    val_yx_s0 = compute_sum(e2, e1, fx, fy)
    diff_s1 = abs(val_xy_s1 - val_yx_s1)
    diff_s0 = abs(val_xy_s0 - val_yx_s0)
    label = f"{name_x}*{name_y}"
    status = "OK" if diff_s1 < 1e-10 and diff_s0 < 1e-10 else "FAIL"
    if status == "FAIL":
        sym_ok = False
    print(f"  {label:16s}: diff_s1={diff_s1:.1e}, diff_s0={diff_s0:.1e}  [{status}]")
print(f"\nSymmetry: {'ALL OK' if sym_ok else 'FAILURES DETECTED'}")

# Verification: reassemble and check against known totals
print("\nReassembly verification:")
print("=" * 60)

# C6a*C6a = C6a1*C6a1 + 2*C6a1*C6a2 + C6a2*C6a2
aa = results[('C6a1','C6a1')]
ab = results[('C6a1','C6a2')]
bb = results[('C6a2','C6a2')]
aa_total = (aa[0] + 2*ab[0] + bb[0], aa[1] + 2*ab[1] + bb[1])
print(f"  C6a*C6a = {aa_total[0]}*s^2 + {aa_total[1]} (expected 1800*s^2)")

# C6a*C6b = C6a1*(C6b1+C6b2+C6b3) + C6a2*(C6b1+C6b2+C6b3)
ab_total_s = sum(results[('C6a1',b)][0] + results[('C6a2',b)][0] for b in ['C6b1','C6b2','C6b3'])
ab_total_c = sum(results[('C6a1',b)][1] + results[('C6a2',b)][1] for b in ['C6b1','C6b2','C6b3'])
print(f"  C6a*C6b = {ab_total_s}*s^2 + {ab_total_c} (expected 720*s^2 + 360)")

# C6b*C6b = all C6bi*C6bj
bb_total_s = 0
bb_total_c = 0
for i, ni in enumerate(['C6b1','C6b2','C6b3']):
    for j, nj in enumerate(['C6b1','C6b2','C6b3']):
        key = (ni, nj) if (ni, nj) in results else (nj, ni)
        mult = 1 if i == j else (2 if i < j else 0)
        if mult > 0:
            bb_total_s += mult * results[key][0]
            bb_total_c += mult * results[key][1]
print(f"  C6b*C6b = {bb_total_s}*s^2 + {bb_total_c} (expected 4320*s^2 + 360)")

# Total C6*C6
total_s = aa_total[0] + 2*ab_total_s + bb_total_s
total_c = aa_total[1] + 2*ab_total_c + bb_total_c
print(f"  Total C6*C6 = {total_s}*s^2 + {total_c} (expected 7560*s^2 + 1080)")
