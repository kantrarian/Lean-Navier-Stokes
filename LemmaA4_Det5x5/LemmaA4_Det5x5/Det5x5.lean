import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strengthened Lemma A.4: explicit 5×5 determinant for joint surjectivity

Source: `Explicit_5x5_Determinant.docx` (R. J. Mathews, April 2026),
supplement to "Two Technical Lemmas". This Lean file formalizes:

* `det_M_A_trace_free` — Lemma 2.1 in the supplement.
* `det_M_B_trace_free` — Lemma 3.1 in the supplement.
* `joint_nonvanishing` — Theorem 4.1 (Strengthened Lemma A.4): at every
  nondegenerate strain configuration on the trace-free stratum, at least
  one of `det(M_A)`, `det(M_B)` is nonzero.

The matrices have entries with `Real.sqrt 3`, so they are `noncomputable`.
The proofs rely only on the Lean / mathlib foundation axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no custom axioms,
no `sorry`, no `admit`.
-/

namespace LemmaA4_Det5x5

open Real Matrix

/-! ## The two response matrices -/

/-- The 5×5 response matrix `M_A` from Table 1 of the supplement.
    Rows F₁…F₅ index functionals (h₁₂, h₁₃, h₂₃, F₄, F₅);
    columns 1…5 index plane waves. -/
noncomputable def M_A (l₁ l₂ l₃ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ (l₁ - l₂) / 4,         0,                 0,                 4 * (l₁ - l₂) / 25,  sqrt 3 * (l₁ - l₃) / 18 ;
      0,                     (l₁ - l₃) / 4,     0,                 0,                   sqrt 3 * (l₁ - l₃) / 36 ;
      0,                     0,                 (l₂ - l₃) / 4,     0,                   sqrt 3 * (l₁ - l₃) / 18 ;
      1,                     1 / 2,             -(1 / 2),          4 / 5,               sqrt 3 / 6              ;
      0,                     0,                 0,                 -(3 / 5),            sqrt 3 / 3              ]

/-- The 5×5 response matrix `M_B` from Table 2 of the supplement.
    Waves 1–3 are shared with Set A; waves 4',5' swap k₁↔k₂, p₁↔p₂. -/
noncomputable def M_B (l₁ l₂ l₃ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ (l₁ - l₂) / 4,         0,                 0,                 4 * (l₁ - l₂) / 25,  sqrt 3 * (l₂ - l₃) / 18 ;
      0,                     (l₁ - l₃) / 4,     0,                 0,                   sqrt 3 * (l₂ - l₃) / 18 ;
      0,                     0,                 (l₂ - l₃) / 4,     0,                   sqrt 3 * (l₂ - l₃) / 36 ;
      1,                     1 / 2,             -(1 / 2),          4 / 5,               -(sqrt 3 / 6)           ;
      0,                     0,                 0,                 3 / 5,               sqrt 3 / 3              ]

/-! ## Determinant identities -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 32000000 in
/-- Lemma 2.1 (Set A determinant, trace-free form).
    On the constraint λ₃ = -λ₁ - λ₂, the determinant factors as
    -(√3/4800) · (2λ₁ + λ₂) · (λ₁² + 46 λ₁ λ₂ + 43 λ₂²). -/
theorem det_M_A_trace_free (l₁ l₂ : ℝ) :
    (M_A l₁ l₂ (-l₁ - l₂)).det =
      -(sqrt 3 / 4800) * (2 * l₁ + l₂) * (l₁ ^ 2 + 46 * l₁ * l₂ + 43 * l₂ ^ 2) := by
  simp only [M_A, det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    submatrix_apply, submatrix_submatrix, det_unique, det_fin_three,
    Fin.default_eq_zero, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_one,
    Fin.succ_succAbove_succ,
    cons_val_zero, cons_val_one, cons_val_succ, cons_val_fin_one, head_cons,
    Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.val_eq_zero,
    pow_zero, pow_one, neg_mul, one_mul, mul_one, zero_mul, mul_zero,
    add_zero, zero_add, Finset.sum_singleton, Finset.sum_const, Finset.card_singleton,
    one_smul, neg_zero, Even.neg_pow, even_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Fin.succAbove,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT]
  simp [Fin.lt_def]
  ring

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 32000000 in
/-- Lemma 3.1 (Set B determinant, trace-free form).
    On the constraint λ₃ = -λ₁ - λ₂, the determinant factors as
    (√3/4800) · (λ₁ + 2λ₂) · (43 λ₁² + 46 λ₁ λ₂ + λ₂²). -/
theorem det_M_B_trace_free (l₁ l₂ : ℝ) :
    (M_B l₁ l₂ (-l₁ - l₂)).det =
      (sqrt 3 / 4800) * (l₁ + 2 * l₂) * (43 * l₁ ^ 2 + 46 * l₁ * l₂ + l₂ ^ 2) := by
  simp only [M_B, det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    submatrix_apply, submatrix_submatrix, det_unique, det_fin_three,
    Fin.default_eq_zero, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_one,
    Fin.succ_succAbove_succ,
    cons_val_zero, cons_val_one, cons_val_succ, cons_val_fin_one, head_cons,
    Fin.isValue, Fin.val_zero, Fin.val_succ, Fin.val_eq_zero,
    pow_zero, pow_one, neg_mul, one_mul, mul_one, zero_mul, mul_zero,
    add_zero, zero_add, Finset.sum_singleton, Finset.sum_const, Finset.card_singleton,
    one_smul, neg_zero, Even.neg_pow, even_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Fin.succAbove,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT]
  simp [Fin.lt_def]
  ring

/-! ## Joint non-vanishing on the nondegenerate stratum -/

/-- Theorem 4.1 (Strengthened Lemma A.4): joint non-vanishing.
    On the trace-free nondegenerate stratum (encoded by the three hypotheses
    `l₁ ≠ l₂` (i.e. λ₁ ≠ λ₂), `2*l₁ + l₂ ≠ 0` (i.e. λ₁ ≠ λ₃ since λ₃ = -λ₁-λ₂),
    and `l₁ + 2*l₂ ≠ 0` (i.e. λ₂ ≠ λ₃)), at least one of `det(M_A)`,
    `det(M_B)` is nonzero.

    Proof. If both vanish, the determinant identities plus the nonzero linear
    factors force both quadratic factors to vanish. Their difference is
    42 (λ₂² - λ₁²), so λ₁² = λ₂². The case `λ₁ = λ₂` contradicts `h12`
    directly; `λ₁ = -λ₂` substituted back into `Q_A` gives -2 λ₁² = 0, hence
    λ₁ = λ₂ = 0, again contradicting `h12`. -/
theorem joint_nonvanishing (l₁ l₂ : ℝ)
    (h12 : l₁ ≠ l₂)
    (h13 : 2 * l₁ + l₂ ≠ 0)
    (h23 : l₁ + 2 * l₂ ≠ 0) :
    (M_A l₁ l₂ (-l₁ - l₂)).det ≠ 0 ∨ (M_B l₁ l₂ (-l₁ - l₂)).det ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨hA, hB⟩ := hc
  rw [det_M_A_trace_free] at hA
  rw [det_M_B_trace_free] at hB
  have hsqrt_pos : (0:ℝ) < sqrt 3 / 4800 := by positivity
  have hsqrt_ne : -(sqrt 3 / 4800) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hsqrt_pos)
  have hsqrt_pos_ne : (sqrt 3 / 4800) ≠ 0 := ne_of_gt hsqrt_pos
  have hQA : l₁ ^ 2 + 46 * l₁ * l₂ + 43 * l₂ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hA with hAB | hC
    · rcases mul_eq_zero.mp hAB with hA0 | hB0
      · exact absurd hA0 hsqrt_ne
      · exact absurd hB0 h13
    · exact hC
  have hQB : 43 * l₁ ^ 2 + 46 * l₁ * l₂ + l₂ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hB with hAB | hC
    · rcases mul_eq_zero.mp hAB with hA0 | hB0
      · exact absurd hA0 hsqrt_pos_ne
      · exact absurd hB0 h23
    · exact hC
  have hsq : l₂ ^ 2 = l₁ ^ 2 := by linarith
  have habs : l₁ = l₂ ∨ l₁ = -l₂ := by
    have hfactor : (l₁ - l₂) * (l₁ + l₂) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · left; linarith
    · right; linarith
  rcases habs with heq | hneg
  · exact h12 heq
  · have hzero : (-2 : ℝ) * l₁ ^ 2 = 0 := by
      have : l₂ = -l₁ := by linarith
      rw [this] at hQA; linarith
    have hl1 : l₁ = 0 := by
      have hl1sq : l₁ ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hl1sq
    have hl2 : l₂ = 0 := by linarith
    exact h12 (hl1.trans hl2.symm)

end LemmaA4_Det5x5
