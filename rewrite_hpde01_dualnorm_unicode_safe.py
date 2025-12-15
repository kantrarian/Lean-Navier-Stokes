from pathlib import Path

# Write Lean using \u escapes in Python source to avoid PowerShell mojibake.
R = "\u211d"      # â„
AR = "\u2192"     # â†’
NORM = "\u2016"   # â€–
SUM = "\u2211"    # âˆ‘
SMUL = "\u2022"   # â€¢
LE = "\u2264"     # â‰¤
FA = "\u2200"     # âˆ€
EX = "\u2203"     # âˆƒ

lean = f"""import Mathlib

/-!
# HPDE_01: Dual norm characterization for Fin 3

For continuous linear functionals on `(Fin 3 {AR} {R})` with the sup norm,
we show the operator norm equals the \u21131 norm of evaluations on the standard basis.

This is used to remove norm-equivalence axioms in HPDE_01.
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
  rcases lt_trichotomy x 0 with hx | hx | hx
  \u00b7 have hx' : \u00ac x > 0 := by exact not_lt.mpr (le_of_lt hx)
    simp [hx, hx', abs_of_neg hx]
    ring
  \u00b7 simp [hx]
  \u00b7 simp [hx, abs_of_pos hx]

/-- Sum of squares \u2264 square of sum of absolute values (Fin 3). -/
lemma sum_sq_le_sq_sum_abs (a : Fin 3 {AR} {R}) :
    ({SUM} i : Fin 3, (a i)^2) {LE} ({SUM} i : Fin 3, |a i|)^2 := by
  simp [Fin.sum_univ_three, pow_two]
  have h01 : 0 {LE} 2 * |a 0| * |a 1| := by positivity
  have h02 : 0 {LE} 2 * |a 0| * |a 2| := by positivity
  have h12 : 0 {LE} 2 * |a 1| * |a 2| := by positivity
  nlinarith

/-- (\u2211|a\u1d62|)^2 \u2264 3 \u22c5 \u2211 a\u1d62^2 (Fin 3). -/
lemma sq_sum_abs_le_three_mul_sum_sq (a : Fin 3 {AR} {R}) :
    ({SUM} i : Fin 3, |a i|)^2 {LE} 3 * ({SUM} i : Fin 3, (a i)^2) := by
  simp [Fin.sum_univ_three, pow_two]
  have h0 := sq_nonneg (|a 0| - |a 1|)
  have h1 := sq_nonneg (|a 0| - |a 2|)
  have h2 := sq_nonneg (|a 1| - |a 2|)
  nlinarith

lemma pi_eq_sum_single (v : Fin 3 {AR} {R}) :
    v = {SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}) := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  \u00b7 simp
  \u00b7 intro i _ hij
    simp [hij]
  \u00b7 intro h
    exact (h (Finset.mem_univ j)).elim

/-- Operator norm equals the \u21131 norm of evaluations on the standard basis (Fin 3). -/
theorem opNorm_eq_sum_abs_fin3 (L : (Fin 3 {AR} {R}) {AR}L[{R}] {R}) :
    {NORM}L{NORM} = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
  apply le_antisymm

  \u00b7 apply ContinuousLinearMap.opNorm_le_bound _ (by
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    intro v
    calc
      {NORM}L v{NORM} = |L v| := by simpa [Real.norm_eq_abs]
      _ = |L ({SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}))| := by
            simpa [pi_eq_sum_single (v := v)]
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

  \u00b7 let v : Fin 3 {AR} {R} := fun i => realSign (L (Pi.single i (1 : {R})))

    have hv_norm : {NORM}v{NORM} {LE} 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : {R}) {LE} 1)]
      intro i
      exact abs_realSign_le_one _

    have hv_eval : L v = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
      calc
        L v = L ({SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R})) := by
              simpa [pi_eq_sum_single (v := v)]
        _ = {SUM} i : Fin 3, v i * L (Pi.single i (1 : {R})) := by
              simp [map_sum, map_smul, smul_eq_mul]
        _ = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp [v, realSign_mul_self]

    calc
      {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))|
          = L v := hv_eval.symm
      _ {LE} {NORM}L v{NORM} := le_norm_self _
      _ {LE} {NORM}L{NORM} * {NORM}v{NORM} := L.le_opNorm v
      _ {LE} {NORM}L{NORM} * 1 := by
            apply mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
      _ = {NORM}L{NORM} := by simp

end HPDE_01
"""

out = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\DualNorm.lean")
out.write_text(lean, encoding="utf-8")
print("rewrote DualNorm.lean (unicode-safe)")