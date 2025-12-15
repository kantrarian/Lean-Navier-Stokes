from pathlib import Path

# Build Lean source as ASCII python, emitting unicode via \u escapes.
R = "\u211d"      # â„
AR = "\u2192"     # â†’
NORM = "\u2016"   # â€–
SUM = "\u2211"    # âˆ‘
SMUL = "\u2022"   # â€¢
LE = "\u2264"     # â‰¤

lean = f"""import Mathlib

/-!
# HPDE_01: Dual norm characterization for `Fin 3 {AR} {R}`

For continuous linear functionals on `(Fin 3 {AR} {R})` with the sup norm,
we prove: `{NORM}L{NORM} = {SUM} i, |L(e_i)|`.

This is used to remove the HPDE_01 norm-equivalence axioms relating `gradientSq`
and `â€–fderivâ€–`.
-/

open scoped BigOperators
open Finset

namespace HPDE_01

noncomputable def realSign (x : {R}) : {R} :=
  if x > 0 then 1 else if x < 0 then -1 else 0

@[simp] lemma realSign_zero : realSign (0 : {R}) = 0 := by
  simp [realSign]

lemma abs_realSign_le_one (x : {R}) : |realSign x| {LE} 1 := by
  unfold realSign
  split_ifs <;> simp

lemma realSign_mul_self (x : {R}) : realSign x * x = |x| := by
  unfold realSign
  by_cases hpos : x > 0
  Â· simp [hpos, abs_of_pos hpos]
  Â· by_cases hneg : x < 0
    Â· have hx' : Â¬ x > 0 := hpos
      simp [hx', hneg, abs_of_neg hneg]
      ring
    Â· have hx0 : x = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [hx0]

/-- Sum of squares â‰¤ square of sum of absolute values (Fin 3). -/
lemma sum_sq_le_sq_sum_abs (a : Fin 3 {AR} {R}) :
    ({SUM} i : Fin 3, (a i)^2) {LE} ({SUM} i : Fin 3, |a i|)^2 := by
  -- Expand sums to 3-term expressions
  simp [Fin.sum_univ_three, pow_two, sq_abs]
  have h01 : 0 {LE} 2 * |a 0| * |a 1| := by positivity
  have h02 : 0 {LE} 2 * |a 0| * |a 2| := by positivity
  have h12 : 0 {LE} 2 * |a 1| * |a 2| := by positivity
  -- RHS = LHS + nonnegative cross terms
  nlinarith

/-- (âˆ‘|aáµ¢|)^2 â‰¤ 3 * âˆ‘ aáµ¢^2 (Fin 3). -/
lemma sq_sum_abs_le_three_mul_sum_sq (a : Fin 3 {AR} {R}) :
    ({SUM} i : Fin 3, |a i|)^2 {LE} 3 * ({SUM} i : Fin 3, (a i)^2) := by
  -- Use Mathlibâ€™s general inequality on finite sums: (âˆ‘ f)^2 â‰¤ card * âˆ‘ f^2.
  -- Apply it to f i = |a i|.
  classical
  have h := Finset.sum_sq_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 3 => |a i|)
  -- `h : (âˆ‘ i, |a i|)^2 â‰¤ card univ * âˆ‘ i, |a i|^2`
  -- Rewrite `|a i|^2` as `(a i)^2`.
  simpa [Fin.sum_univ_three, sq_abs, Finset.card_fin, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

lemma pi_eq_sum_single (v : Fin 3 {AR} {R}) :
    v = {SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}) := by
  classical
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  Â· simp
  Â· intro i _ hij
    simp [hij]
  Â· intro h
    exact (h (Finset.mem_univ j)).elim

/-- Operator norm equals â„“Â¹ norm of basis evaluations (Fin 3, sup norm on domain). -/
theorem opNorm_eq_sum_abs_fin3 (L : (Fin 3 {AR} {R}) {AR}L[{R}] {R}) :
    {NORM}L{NORM} = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
  classical
  apply le_antisymm

  Â· -- upper bound: triangle inequality + `norm_le_pi_norm`
    apply ContinuousLinearMap.opNorm_le_bound _ (by
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    intro v
    have hv : v = {SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}) := pi_eq_sum_single (v := v)
    calc
      {NORM}L v{NORM}
          = |L v| := by simpa [Real.norm_eq_abs]
      _ = |L ({SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}))| := by simpa [hv]
      _ = |{SUM} i : Fin 3, v i * L (Pi.single i (1 : {R}))| := by
            simp [map_sum, map_smul, smul_eq_mul]
      _ {LE} {SUM} i : Fin 3, |v i * L (Pi.single i (1 : {R}))| := by
            simpa using (abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun i : Fin 3 => v i * L (Pi.single i (1 : {R}))))
      _ = {SUM} i : Fin 3, |v i| * |L (Pi.single i (1 : {R}))| := by
            simp [abs_mul]
      _ {LE} {SUM} i : Fin 3, {NORM}v{NORM} * |L (Pi.single i (1 : {R}))| := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (abs_nonneg _)
      _ = {NORM}v{NORM} * ({SUM} i : Fin 3, |L (Pi.single i (1 : {R}))|) := by
            simp [Finset.mul_sum]

  Â· -- lower bound: choose the sign vector
    let v : Fin 3 {AR} {R} := fun i => realSign (L (Pi.single i (1 : {R})))

    have hv_norm : {NORM}v{NORM} {LE} 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : {R}) {LE} 1)]
      intro i
      exact abs_realSign_le_one _

    have hv_eval : L v = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
      have hv : v = {SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}) := pi_eq_sum_single (v := v)
      calc
        L v = L ({SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R})) := by simpa [hv]
        _ = {SUM} i : Fin 3, v i * L (Pi.single i (1 : {R})) := by
              simp [map_sum, map_smul, smul_eq_mul]
        _ = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp [v, realSign_mul_self]

    have hOp : {NORM}L v{NORM} {LE} {NORM}L{NORM} * {NORM}v{NORM} := L.le_opNorm v

    calc
      {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))|
          = L v := hv_eval.symm
      _ {LE} |L v| := le_abs_self _
      _ = {NORM}L v{NORM} := by simpa [Real.norm_eq_abs]
      _ {LE} {NORM}L{NORM} * {NORM}v{NORM} := hOp
      _ {LE} {NORM}L{NORM} * 1 := by
            apply mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
      _ = {NORM}L{NORM} := by simp

end HPDE_01
"""

out = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\DualNorm.lean")
out.write_text(lean, encoding="utf-8")
print("wrote DualNorm.lean v2")