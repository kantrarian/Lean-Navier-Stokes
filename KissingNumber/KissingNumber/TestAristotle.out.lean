/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 84b515e2-11aa-4568-ac7d-1c10523cdc80

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import KissingNumber.PSD6Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


open scoped BigOperators RealInnerProductSpace

open Real Finset

open PSD6Defs

noncomputable section

private abbrev T6k := PSD6Defs.T6

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

`simp` made no progress-/
-- sum_AD: After simp chain + r-rules + factor3 + hxn, need to close `norm_num`
-- The goal state after the simp chain is: residual 3-fold sums that each = 1, total = 15
set_option maxHeartbeats 800000000 in
private lemma sum_AD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6k, A6 x p * D6 y p = 15 := by
  have hxn := ofLp_norm_sq x hx
  simp only [A6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 200000000 }) only [mul_ite, mul_zero, mul_one]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have r1 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r2 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r3 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp b * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  simp_rw [r1, r2, r3, factor3, hxn]
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Receive failed with exception TimeoutError(); partial output: -/
-- sum_BD: After simp chain + r-rules + factor2 + hxn, need to close
set_option maxHeartbeats 800000000 in
private lemma sum_BD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6 x p * D6 y p =
    (540 : ℝ) := by
  have hxn := ofLp_norm_sq x hx
  simp only [B6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 200000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have r1 : ∀ a b : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r3 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, factor2, hxn]
  sorry

end