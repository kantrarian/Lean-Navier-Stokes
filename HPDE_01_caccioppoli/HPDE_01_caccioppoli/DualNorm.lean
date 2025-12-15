import Mathlib
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace HPDE_01

noncomputable def realSign (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x < 0 then -1 else 0

@[simp] lemma realSign_zero : realSign (0 : ℝ) = 0 := by
  simp [realSign]

lemma abs_realSign_le_one (x : ℝ) : |realSign x| ≤ 1 := by
  unfold realSign
  split_ifs <;> simp

lemma realSign_mul_self (x : ℝ) : realSign x * x = |x| := by
  unfold realSign
  by_cases hpos : x > 0 <;> by_cases hneg : x < 0 <;> simp [hpos, hneg]

lemma sum_sq_le_sq_sum_abs (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, (a i)^2) ≤ (∑ i : Fin 3, |a i|)^2 := by
  simp [Fin.sum_univ_three, pow_two, sq_abs]
  have h01 : 0 ≤ 2 * |a 0| * |a 1| := by positivity
  have h02 : 0 ≤ 2 * |a 0| * |a 2| := by positivity
  have h12 : 0 ≤ 2 * |a 1| * |a 2| := by positivity
  nlinarith

lemma sq_sum_abs_le_three_mul_sum_sq (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, |a i|)^2 ≤ 3 * (∑ i : Fin 3, (a i)^2) := by
  have h01 : 2 * |a 0| * |a 1| ≤ |a 0|^2 + |a 1|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 1|)]
  have h02 : 2 * |a 0| * |a 2| ≤ |a 0|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 2|)]
  have h12 : 2 * |a 1| * |a 2| ≤ |a 1|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 1| - |a 2|)]
  simp [Fin.sum_univ_three, pow_two, sq_abs]
  nlinarith [h01, h02, h12]

lemma pi_eq_sum_single (v : Fin 3 → ℝ) :
    v = ∑ i : Fin 3, v i • Pi.single i (1 : ℝ) := by
  funext j
  -- expand the sum over Fin 3 and evaluate Pi.single
  simp [Fin.sum_univ_three, Pi.single_apply, smul_eq_mul]

theorem opNorm_eq_sum_abs_fin3 (L : (Fin 3 → ℝ) →L[ℝ] ℝ) :
    ‖L‖ = ∑ i : Fin 3, |L (Pi.single i (1 : ℝ))| := by
  classical
  refine le_antisymm
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ (by
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      intro v
      have hv : v = ∑ i : Fin 3, v i • Pi.single i (1 : ℝ) := by
        ext j
        simpa using congrArg (fun f => f j) (pi_eq_sum_single (v := v))
      calc
        ‖L v‖ = |L v| := by simpa [Real.norm_eq_abs]
        _ = |L (∑ i : Fin 3, v i • Pi.single i (1 : ℝ))| := by simpa [hv]
        _ = |∑ i : Fin 3, v i * L (Pi.single i (1 : ℝ))| := by
              simp [map_sum, map_smul, smul_eq_mul]
        _ ≤ ∑ i : Fin 3, |v i * L (Pi.single i (1 : ℝ))| := by
              simpa using (abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun i : Fin 3 => v i * L (Pi.single i (1 : ℝ))))
        _ = ∑ i : Fin 3, |v i| * |L (Pi.single i (1 : ℝ))| := by
              simp [abs_mul]
        _ ≤ ∑ i : Fin 3, ‖v‖ * |L (Pi.single i (1 : ℝ))| := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (abs_nonneg _)
        _ = ‖v‖ * (∑ i : Fin 3, |L (Pi.single i (1 : ℝ))|) := by
              simp [Finset.mul_sum])
    (by
      let v : Fin 3 → ℝ := fun i => realSign (L (Pi.single i (1 : ℝ)))
      have hv_norm : ‖v‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
        intro i
        exact abs_realSign_le_one _
      have hv_eval : L v = ∑ i : Fin 3, |L (Pi.single i (1 : ℝ))| := by
        calc
          L v = L (∑ i : Fin 3, v i • Pi.single i (1 : ℝ)) := by
                simpa using congrArg L (pi_eq_sum_single (v := v))
          _ = ∑ i : Fin 3, v i * L (Pi.single i (1 : ℝ)) := by
                simp [map_sum, map_smul, smul_eq_mul]
          _ = ∑ i : Fin 3, |L (Pi.single i (1 : ℝ))| := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                simp [v, realSign_mul_self]
      calc
        ∑ i : Fin 3, |L (Pi.single i (1 : ℝ))|
            = L v := hv_eval.symm
        _ ≤ |L v| := le_abs_self _
        _ = ‖L v‖ := by simpa [Real.norm_eq_abs]
        _ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
        _ ≤ ‖L‖ * 1 := by
              apply mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
        _ = ‖L‖ := by simp)

end HPDE_01
