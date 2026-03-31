"""
Verify PSD feature map constants for d=5, k=4 and k=5.

For each k, we determine:
- The coefficients alpha, beta in phi_k = A_k - alpha*B_k + beta*C_k
- The kernel constant c such that sum phi_k(x)*phi_k(y) = c * P5_k(<x,y>)
- All cross-term sum values (AA, AB, AC, BB, BC, CC)

Method: Numerical evaluation on random unit vectors in R^5.
"""

import numpy as np
from itertools import product as cart_product
from fractions import Fraction


def random_unit_vector(d):
    v = np.random.randn(d)
    return v / np.linalg.norm(v)


def compute_cross_sums_k4(x, y, d):
    """Compute all cross-term sums for k=4 trace-free tensors in R^d."""
    s = np.dot(x, y)
    
    # A4(x,p) = x[a]*x[b]*x[c]*x[d]
    # B4(x,p) = sum of 6 terms: x[i]*x[j]*delta(k,l)
    # C4(x,p) = delta(a,b)*delta(c,d) + delta(a,c)*delta(b,d) + delta(a,d)*delta(b,c)
    
    sum_AA = 0.0
    sum_AB = 0.0
    sum_AC = 0.0
    sum_BB = 0.0
    sum_BC = 0.0
    sum_CC = 0.0
    
    for a in range(d):
        for b in range(d):
            for c in range(d):
                for dd in range(d):
                    Ax = x[a]*x[b]*x[c]*x[dd]
                    Ay = y[a]*y[b]*y[c]*y[dd]
                    
                    # B4 terms
                    def delta(i,j): return 1.0 if i==j else 0.0
                    Bx = (x[c]*x[dd]*delta(a,b) + x[b]*x[dd]*delta(a,c) + 
                          x[b]*x[c]*delta(a,dd) + x[a]*x[dd]*delta(b,c) + 
                          x[a]*x[c]*delta(b,dd) + x[a]*x[b]*delta(c,dd))
                    By = (y[c]*y[dd]*delta(a,b) + y[b]*y[dd]*delta(a,c) + 
                          y[b]*y[c]*delta(a,dd) + y[a]*y[dd]*delta(b,c) + 
                          y[a]*y[c]*delta(b,dd) + y[a]*y[b]*delta(c,dd))
                    
                    # C4 terms (no x/y dependence)
                    Cx = (delta(a,b)*delta(c,dd) + delta(a,c)*delta(b,dd) + 
                          delta(a,dd)*delta(b,c))
                    Cy = Cx  # Same since it doesn't depend on x or y
                    
                    sum_AA += Ax * Ay
                    sum_AB += Ax * By
                    sum_AC += Ax * Cy
                    sum_BB += Bx * By
                    sum_BC += Bx * Cy
                    sum_CC += Cx * Cy
    
    return {
        'AA': sum_AA, 'AB': sum_AB, 'AC': sum_AC,
        'BB': sum_BB, 'BC': sum_BC, 'CC': sum_CC,
        's': s, 's2': s**2, 's4': s**4
    }


def compute_cross_sums_k5(x, y, d):
    """Compute cross-term sums for k=5 in R^d."""
    s = np.dot(x, y)
    
    sum_AA = 0.0
    sum_AB = 0.0
    sum_AC = 0.0
    sum_BB = 0.0
    sum_BC = 0.0
    sum_CC = 0.0
    
    def delta(i,j): return 1.0 if i==j else 0.0
    
    indices = range(d)
    
    for a in indices:
        for b in indices:
            for c in indices:
                for dd in indices:
                    for e in indices:
                        idx = [a,b,c,dd,e]
                        
                        # A5
                        Ax = x[a]*x[b]*x[c]*x[dd]*x[e]
                        Ay = y[a]*y[b]*y[c]*y[dd]*y[e]
                        
                        # B5: C(5,2) = 10 terms
                        Bx = 0.0
                        By = 0.0
                        for i in range(5):
                            for j in range(i+1, 5):
                                # delta at positions i,j; x at remaining 3
                                d_val = delta(idx[i], idx[j])
                                remaining = [idx[k] for k in range(5) if k != i and k != j]
                                Bx += d_val * x[remaining[0]] * x[remaining[1]] * x[remaining[2]]
                                By += d_val * y[remaining[0]] * y[remaining[1]] * y[remaining[2]]
                        
                        # C5: 5 * 3 = 15 terms
                        # For each unpaired position k, and each pairing of the remaining 4
                        Cx = 0.0
                        Cy = 0.0
                        for k_pos in range(5):
                            others = [idx[j] for j in range(5) if j != k_pos]
                            # 3 pairings of 4 elements: (01)(23), (02)(13), (03)(12)
                            pairings = [((0,1),(2,3)), ((0,2),(1,3)), ((0,3),(1,2))]
                            for (p1,p2),(p3,p4) in pairings:
                                d_prod = delta(others[p1], others[p2]) * delta(others[p3], others[p4])
                                Cx += x[idx[k_pos]] * d_prod
                                Cy += y[idx[k_pos]] * d_prod
                        
                        sum_AA += Ax * Ay
                        sum_AB += Ax * By
                        sum_AC += Ax * Cy
                        sum_BB += Bx * By
                        sum_BC += Bx * Cy
                        sum_CC += Cx * Cy
    
    return {
        'AA': sum_AA, 'AB': sum_AB, 'AC': sum_AC,
        'BB': sum_BB, 'BC': sum_BC, 'CC': sum_CC,
        's': s, 's3': s**3, 's5': s**5
    }


def main():
    np.random.seed(42)
    d = 5
    
    print("=" * 70)
    print("PSD CONSTANT VERIFICATION FOR d=5")
    print("=" * 70)
    
    # ========== k = 4 ==========
    print("\n--- k = 4 ---")
    
    # Test multiple random vectors
    for trial in range(3):
        x = random_unit_vector(d)
        y = random_unit_vector(d)
        sums = compute_cross_sums_k4(x, y, d)
        s = sums['s']
        
        print(f"\nTrial {trial+1}: s = {s:.6f}")
        print(f"  AA = {sums['AA']:.8f}, expected s^4 = {s**4:.8f}, match: {abs(sums['AA'] - s**4) < 1e-10}")
        print(f"  AB = {sums['AB']:.8f}, expected 6s^2 = {6*s**2:.8f}, match: {abs(sums['AB'] - 6*s**2) < 1e-10}")
        print(f"  AC = {sums['AC']:.8f}, expected 3 = 3.0, match: {abs(sums['AC'] - 3) < 1e-10}")
        
        # Fit BB = a*s^2 + b
        # We'll compute from the formula: (6d+24)s^2 + 6
        bb_expected = (6*d + 24)*s**2 + 6
        print(f"  BB = {sums['BB']:.8f}, expected {bb_expected:.8f} (54s^2+6), match: {abs(sums['BB'] - bb_expected) < 1e-8}")
        
        # Fit BC = 6d + 12 = 42
        bc_expected = 6*d + 12
        print(f"  BC = {sums['BC']:.8f}, expected {bc_expected}, match: {abs(sums['BC'] - bc_expected) < 1e-8}")
        
        # CC = 3d^2 + 6d = 75 + 30 = 105
        cc_expected = 3*d**2 + 6*d
        print(f"  CC = {sums['CC']:.8f}, expected {cc_expected}, match: {abs(sums['CC'] - cc_expected) < 1e-8}")
    
    # Verify kernel with alpha=1/9, beta=1/63
    alpha4 = Fraction(1, 9)
    beta4 = Fraction(1, 63)
    c4 = Fraction(8, 21)
    
    print(f"\nk=4 constants: alpha={alpha4}, beta={beta4}, c={c4}")
    
    x = random_unit_vector(d)
    y = random_unit_vector(d)
    sums = compute_cross_sums_k4(x, y, d)
    s = sums['s']
    
    # Kernel = AA - 2*alpha*AB + 2*beta*AC + alpha^2*BB - 2*alpha*beta*BC + beta^2*CC
    kernel = (sums['AA'] - 2*float(alpha4)*sums['AB'] + 2*float(beta4)*sums['AC']
             + float(alpha4)**2*sums['BB'] - 2*float(alpha4)*float(beta4)*sums['BC']
             + float(beta4)**2*sums['CC'])
    
    # P5_4(s) = (21*s^4 - 14*s^2 + 1)/8
    P5_4 = (21*s**4 - 14*s**2 + 1)/8
    expected = float(c4) * P5_4
    
    print(f"\nKernel verification:")
    print(f"  sum phi4*phi4 = {kernel:.10f}")
    print(f"  (8/21)*P5_4(s) = {expected:.10f}")
    print(f"  Match: {abs(kernel - expected) < 1e-8}")
    
    # ========== k = 5 ==========
    print("\n\n--- k = 5 ---")
    
    # Predicted constants
    alpha5 = Fraction(1, 11)
    beta5 = Fraction(1, 99)
    c5 = Fraction(8, 33)
    
    print(f"k=5 predicted: alpha={alpha5}, beta={beta5}, c={c5}")
    
    for trial in range(2):
        x = random_unit_vector(d)
        y = random_unit_vector(d)
        sums = compute_cross_sums_k5(x, y, d)
        s = sums['s']
        
        print(f"\nTrial {trial+1}: s = {s:.6f}")
        print(f"  AA = {sums['AA']:.8f}, expected s^5 = {s**5:.8f}, match: {abs(sums['AA'] - s**5) < 1e-8}")
        print(f"  AB = {sums['AB']:.8f}, expected 10s^3 = {10*s**3:.8f}, match: {abs(sums['AB'] - 10*s**3) < 1e-8}")
        
        # AC expected: 15s
        print(f"  AC = {sums['AC']:.8f}, expected 15s = {15*s:.8f}, match: {abs(sums['AC'] - 15*s) < 1e-8}")
        
        # BB for k=5, d=5: need to determine
        # From d=8 pattern: BB = 140s^3 + 30s
        # General: for degree k with C(k,2) delta pairs in dimension d
        # The formula involves: same-pair(d contributions), 1-shared, 0-shared terms
        
        # CC for k=5, d=5: need to determine
        
        # Kernel check
        kernel = (sums['AA'] - 2*float(alpha5)*sums['AB'] + 2*float(beta5)*sums['AC']
                 + float(alpha5)**2*sums['BB'] - 2*float(alpha5)*float(beta5)*sums['BC']
                 + float(beta5)**2*sums['CC'])
        
        P5_5 = (33*s**5 - 30*s**3 + 5*s)/8
        expected = float(c5) * P5_5
        
        print(f"  Kernel = {kernel:.10f}")
        print(f"  (8/33)*P5_5(s) = {expected:.10f}")
        print(f"  Match: {abs(kernel - expected) < 1e-6}")
        
        # Also extract cross-sum formulas by fitting
        # BB should be of form: a*s^3 + b*s
        # BC should be of form: a*s (or constant)
        # CC should be of form: a*s + b (or constant)
    
    # Fit BB for k=5, d=5 from multiple samples
    print("\n\nFitting cross-term formulas for k=5, d=5:")
    
    bb_data = []
    bc_data = []
    cc_data = []
    for _ in range(10):
        x = random_unit_vector(d)
        y = random_unit_vector(d)
        sums = compute_cross_sums_k5(x, y, d)
        s = sums['s']
        bb_data.append((s, sums['BB']))
        bc_data.append((s, sums['BC']))
        cc_data.append((s, sums['CC']))
    
    # Fit BB = a*s^3 + b*s
    A_bb = np.array([[s**3, s] for s, _ in bb_data])
    b_bb = np.array([v for _, v in bb_data])
    coeffs_bb = np.linalg.lstsq(A_bb, b_bb, rcond=None)[0]
    print(f"  BB ~ {coeffs_bb[0]:.2f}*s^3 + {coeffs_bb[1]:.2f}*s")
    
    # Fit BC = a*s
    A_bc = np.array([[s] for s, _ in bc_data])
    b_bc = np.array([v for _, v in bc_data])
    coeffs_bc = np.linalg.lstsq(A_bc, b_bc, rcond=None)[0]
    print(f"  BC ~ {coeffs_bc[0]:.2f}*s")
    
    # Fit CC = a*s
    A_cc = np.array([[s] for s, _ in cc_data])
    b_cc = np.array([v for _, v in cc_data])
    coeffs_cc = np.linalg.lstsq(A_cc, b_cc, rcond=None)[0]
    print(f"  CC ~ {coeffs_cc[0]:.2f}*s")
    
    # Try exact rational values
    for name, coeffs, basis_str in [
        ("BB", coeffs_bb, "s^3, s"),
        ("BC", coeffs_bc, "s"),
        ("CC", coeffs_cc, "s")
    ]:
        print(f"\n  {name} rational approximations:")
        for i, c in enumerate(coeffs):
            frac = Fraction(c).limit_denominator(100)
            print(f"    coeff[{i}] = {c:.6f} ~= {frac}")


if __name__ == "__main__":
    main()
