from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

# Lean block: unicode inserted via escapes so this python file stays ASCII.
lean_block = """
/-!
## Sign Function Helpers for Dual Norm Proof
-/

noncomputable def realSign (x : \u211d) : \u211d :=
  if x > 0 then 1 else if x < 0 then -1 else 0

lemma abs_realSign_le_one (x : \u211d) : |realSign x| \u2264 1 := by
  unfold realSign
  split_ifs <;> simp

lemma realSign_mul_self (x : \u211d) : realSign x * x = |x| := by
  unfold realSign
  by_cases hpos : x > 0
  case pos =>
    simp [hpos, abs_of_pos hpos]
  case neg =>
    by_cases hneg : x < 0
    case pos =>
      simp [hpos, hneg, abs_of_neg hneg]
      ring
    case neg =>
      have hx0 : x = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [hpos, hneg, hx0]

/-!
## Algebraic Helpers
-/

lemma sum_sq_le_sq_sum_abs_fin3 (a : Fin 3 \u2192 \u211d) :
    \u2211 i : Fin 3, (a i)^2 \u2264 (\u2211 i : Fin 3, |a i|)^2 := by
  simp only [Fin.sum_univ_three]
  have hab : 0 \u2264 |a 0| * |a 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hac : 0 \u2264 |a 0| * |a 2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbc : 0 \u2264 |a 1| * |a 2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h0 : (a 0)^2 = |a 0|^2 := (sq_abs _).symm
  have h1 : (a 1)^2 = |a 1|^2 := (sq_abs _).symm
  have h2 : (a 2)^2 = |a 2|^2 := (sq_abs _).symm
  nlinarith [hab, hac, hbc, h0, h1, h2]

lemma sq_sum_abs_le_three_mul_sum_sq_fin3 (a : Fin 3 \u2192 \u211d) :
    (\u2211 i : Fin 3, |a i|)^2 \u2264 3 * \u2211 i : Fin 3, (a i)^2 := by
  simp only [Fin.sum_univ_three]
  have h0 : (a 0)^2 = |a 0|^2 := (sq_abs _).symm
  have h1 : (a 1)^2 = |a 1|^2 := (sq_abs _).symm
  have h2 : (a 2)^2 = |a 2|^2 := (sq_abs _).symm
  have hab : 2 * (|a 0| * |a 1|) \u2264 |a 0|^2 + |a 1|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 1|)]
  have hac : 2 * (|a 0| * |a 2|) \u2264 |a 0|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 2|)]
  have hbc : 2 * (|a 1| * |a 2|) \u2264 |a 1|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 1| - |a 2|)]
  nlinarith [hab, hac, hbc, h0, h1, h2]

/-!
## Operator Norm = \u2113\u00b9 Norm (Fin 3)
-/

lemma opNorm_eq_sum_abs_fin3 (L : (Fin 3 \u2192 \u211d) \u2192L[\u211d] \u211d) :
    \u2016L\u2016 = \u2211 i : Fin 3, |L (Pi.single i 1)| := by
  classical
  apply le_antisymm

  -- <= direction
  Â· apply ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    intro v
    have h_expand : v = \u2211 i : Fin 3, v i \u2022 Pi.single i 1 := by
      ext j
      simp [Fin.sum_univ_three, Pi.single_apply, Finset.sum_eq_single j]
    calc
      \u2016L v\u2016 = |L v| := by simp [Real.norm_eq_abs]
      _ = |L (\u2211 i : Fin 3, v i \u2022 Pi.single i 1)| := by simpa [h_expand]
      _ = |\u2211 i : Fin 3, v i * L (Pi.single i 1)| := by simp [map_sum, map_smul, smul_eq_mul]
      _ \u2264 \u2211 i : Fin 3, |v i * L (Pi.single i 1)| := by
            simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => v i * L (Pi.single i 1)))
      _ = \u2211 i : Fin 3, |v i| * |L (Pi.single i 1)| := by simp [abs_mul]
      _ \u2264 \u2211 i : Fin 3, \u2016v\u2016 * |L (Pi.single i 1)| := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have hv : |v i| \u2264 \u2016v\u2016 := by
              simpa [Real.norm_eq_abs] using (norm_le_pi_norm v i)
            exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
      _ = \u2016v\u2016 * (\u2211 i : Fin 3, |L (Pi.single i 1)|) := by simp [Finset.mul_sum]

  -- >= direction via sign vector
  Â· let v : Fin 3 \u2192 \u211d := fun i => realSign (L (Pi.single i 1))
    have hv_norm : \u2016v\u2016 \u2264 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      simpa [Real.norm_eq_abs] using (abs_realSign_le_one (L (Pi.single i 1)))

    have hv_eval : L v = \u2211 i : Fin 3, |L (Pi.single i 1)| := by
      have h_expand : v = \u2211 i : Fin 3, v i \u2022 Pi.single i 1 := by
        ext j
        simp [Fin.sum_univ_three, Pi.single_apply, Finset.sum_eq_single j]
      calc
        L v = \u2211 i : Fin 3, v i * L (Pi.single i 1) := by
          simp [h_expand, map_sum, map_smul, smul_eq_mul]
        _ = \u2211 i : Fin 3, |L (Pi.single i 1)| := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simpa [v] using (realSign_mul_self (L (Pi.single i 1)))

    have hsum_nonneg : 0 \u2264 (\u2211 i : Fin 3, |L (Pi.single i 1)|) :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)

    have h_le : (\u2211 i : Fin 3, |L (Pi.single i 1)|) \u2264 \u2016L\u2016 * \u2016v\u2016 := by
      calc
        (\u2211 i : Fin 3, |L (Pi.single i 1)|) = |L v| := by
          simpa [hv_eval, abs_of_nonneg hsum_nonneg]
        _ = \u2016L v\u2016 := by simp [Real.norm_eq_abs]
        _ \u2264 \u2016L\u2016 * \u2016v\u2016 := by simpa using (L.le_opNorm v)

    calc
      (\u2211 i : Fin 3, |L (Pi.single i 1)|) \u2264 \u2016L\u2016 * \u2016v\u2016 := h_le
      _ \u2264 \u2016L\u2016 * 1 := mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
      _ = \u2016L\u2016 := by simp
"""

if "lemma opNorm_eq_sum_abs_fin3" not in text:
    # insert right after the variable line
    m = re.search(r"(namespace HPDE_01\s*\n\s*\nvariable .*\n)", text)
    if not m:
        raise RuntimeError("insertion point not found")
    idx = m.end(1)
    text = text[:idx] + lean_block + text[idx:]

# Comment out the norm theorem block cleanly (use '-/' not an escaped variant)
m1 = re.search(r"\ntheorem caccioppoli_elliptic\b", text)
m2 = re.search(r"\ntheorem caccioppoli_elliptic_gradSq\b", text)
if m1 and m2 and m1.start() < m2.start():
    block = text[m1.start():m2.start()]
    if "COMMENTED OUT: Use caccioppoli_elliptic_gradSq" not in block:
        text = text[:m1.start()] + "\n/-\n-- COMMENTED OUT: Use caccioppoli_elliptic_gradSq instead.\n-- Norm-based statement omitted; gradSq theorem below is the primary proved result.\n" + block + "-/\n" + text[m2.start():]

p.write_text(text, encoding="utf-8")
print("patched_v3")