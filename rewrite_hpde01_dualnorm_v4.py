from pathlib import Path

R = "\u211d"      # â„
AR = "\u2192"     # â†’
NORM = "\u2016"   # â€–
SUM = "\u2211"    # âˆ‘
SMUL = "\u2022"   # â€¢
LE = "\u2264"     # â‰¤

lean = f"""import Mathlib
import Mathlib.Tactic

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
  by_cases hpos : x > 0 <;> by_cases hneg : x < 0 <;> simp [hpos, hneg]

lemma sum_sq_le_sq_sum_abs (a : Fin 3 {AR} {R}) :
    ({SUM} i : Fin 3, (a i)^2) {LE} ({SUM} i : Fin 3, |a i|)^2 := by
  simp [Fin.sum_univ_three, pow_two, sq_abs]
  have h01 : 0 {LE} 2 * |a 0| * |a 1| := by positivity
  have h02 : 0 {LE} 2 * |a 0| * |a 2| := by positivity
  have h12 : 0 {LE} 2 * |a 1| * |a 2| := by positivity
  nlinarith

lemma sq_sum_abs_le_three_mul_sum_sq (a : Fin 3 {AR} {R}) :
    ({SUM} i : Fin 3, |a i|)^2 {LE} 3 * ({SUM} i : Fin 3, (a i)^2) := by
  have h01 : 2 * |a 0| * |a 1| {LE} |a 0|^2 + |a 1|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 1|)]
  have h02 : 2 * |a 0| * |a 2| {LE} |a 0|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 2|)]
  have h12 : 2 * |a 1| * |a 2| {LE} |a 1|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 1| - |a 2|)]
  simp [Fin.sum_univ_three, pow_two, sq_abs]
  nlinarith [h01, h02, h12]

lemma pi_eq_sum_single (v : Fin 3 {AR} {R}) :
    v = {SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}) := by
  funext j
  -- expand the sum over Fin 3 and evaluate Pi.single
  simp [Fin.sum_univ_three, Pi.single_apply, smul_eq_mul]

theorem opNorm_eq_sum_abs_fin3 (L : (Fin 3 {AR} {R}) {AR}L[{R}] {R}) :
    {NORM}L{NORM} = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
  classical
  refine le_antisymm
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ (by
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      intro v
      have hv : v = {SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R}) := by
        ext j
        simpa using congrArg (fun f => f j) (pi_eq_sum_single (v := v))
      calc
        {NORM}L v{NORM} = |L v| := by simpa [Real.norm_eq_abs]
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
              simp [Finset.mul_sum])
    (by
      let v : Fin 3 {AR} {R} := fun i => realSign (L (Pi.single i (1 : {R})))
      have hv_norm : {NORM}v{NORM} {LE} 1 := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : {R}) {LE} 1)]
        intro i
        exact abs_realSign_le_one _
      have hv_eval : L v = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
        calc
          L v = L ({SUM} i : Fin 3, v i {SMUL} Pi.single i (1 : {R})) := by
                simpa using congrArg L (pi_eq_sum_single (v := v))
          _ = {SUM} i : Fin 3, v i * L (Pi.single i (1 : {R})) := by
                simp [map_sum, map_smul, smul_eq_mul]
          _ = {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))| := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                simp [v, realSign_mul_self]
      calc
        {SUM} i : Fin 3, |L (Pi.single i (1 : {R}))|
            = L v := hv_eval.symm
        _ {LE} |L v| := le_abs_self _
        _ = {NORM}L v{NORM} := by simpa [Real.norm_eq_abs]
        _ {LE} {NORM}L{NORM} * {NORM}v{NORM} := L.le_opNorm v
        _ {LE} {NORM}L{NORM} * 1 := by
              apply mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
        _ = {NORM}L{NORM} := by simp)

end HPDE_01
"""

out = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\DualNorm.lean")
out.write_text(lean, encoding="utf-8")
print("wrote DualNorm.lean v4")