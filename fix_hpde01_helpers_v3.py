from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

# Replace realSign_mul_self lemma body to avoid extra `ring` and ensure clean cases.
new_realSign_mul = """
lemma realSign_mul_self (x : â„) : realSign x * x = |x| := by
  unfold realSign
  by_cases hpos : x > 0
  case pos =>
    simp [hpos, abs_of_pos hpos]
  case neg =>
    by_cases hneg : x < 0
    case pos =>
      -- in the negative case, `simp` already closes after rewriting abs
      simp [hpos, hneg, abs_of_neg hneg]
    case neg =>
      have hx0 : x = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [hpos, hneg, hx0]
"""

text = re.sub(
    r"lemma realSign_mul_self\s*\(x\s*:\s*â„\)\s*:[\s\S]*?\n\n",
    new_realSign_mul + "\n",
    text,
    count=1,
)

# Replace opNorm_eq_sum_abs_fin3 lemma with a bullet-free proof.
# We avoid `Â·` bullets entirely by constructing the two inequalities as named `have`s.
new_opNorm = """
lemma opNorm_eq_sum_abs_fin3 (L : (Fin 3 â†’ â„) â†’L[â„] â„) :
    â€–Lâ€– = âˆ‘ i : Fin 3, |L (Pi.single i 1)| := by
  classical
  have h_le1 : â€–Lâ€– â‰¤ âˆ‘ i : Fin 3, |L (Pi.single i 1)| := by
    apply ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    intro v
    have h_expand : v = âˆ‘ i : Fin 3, v i â€¢ Pi.single i 1 := by
      ext j
      simp [Fin.sum_univ_three, Pi.single_apply, Finset.sum_eq_single j]
    calc
      â€–L vâ€– = |L v| := by simp [Real.norm_eq_abs]
      _ = |L (âˆ‘ i : Fin 3, v i â€¢ Pi.single i 1)| := by simpa [h_expand]
      _ = |âˆ‘ i : Fin 3, v i * L (Pi.single i 1)| := by simp [map_sum, map_smul, smul_eq_mul]
      _ â‰¤ âˆ‘ i : Fin 3, |v i * L (Pi.single i 1)| := by
            simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => v i * L (Pi.single i 1)))
      _ = âˆ‘ i : Fin 3, |v i| * |L (Pi.single i 1)| := by simp [abs_mul]
      _ â‰¤ âˆ‘ i : Fin 3, â€–vâ€– * |L (Pi.single i 1)| := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have hv : |v i| â‰¤ â€–vâ€– := by
              simpa [Real.norm_eq_abs] using (norm_le_pi_norm v i)
            exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
      _ = â€–vâ€– * (âˆ‘ i : Fin 3, |L (Pi.single i 1)|) := by simp [Finset.mul_sum]

  have h_le2 : (âˆ‘ i : Fin 3, |L (Pi.single i 1)|) â‰¤ â€–Lâ€– := by
    let v : Fin 3 â†’ â„ := fun i => realSign (L (Pi.single i 1))
    have hv_norm : â€–vâ€– â‰¤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      simpa [Real.norm_eq_abs] using (abs_realSign_le_one (L (Pi.single i 1)))

    have hv_eval : L v = âˆ‘ i : Fin 3, |L (Pi.single i 1)| := by
      have h_expand : v = âˆ‘ i : Fin 3, v i â€¢ Pi.single i 1 := by
        ext j
        simp [Fin.sum_univ_three, Pi.single_apply, Finset.sum_eq_single j]
      calc
        L v = âˆ‘ i : Fin 3, v i * L (Pi.single i 1) := by
          simp [h_expand, map_sum, map_smul, smul_eq_mul]
        _ = âˆ‘ i : Fin 3, |L (Pi.single i 1)| := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simpa [v] using (realSign_mul_self (L (Pi.single i 1)))

    have hsum_nonneg : 0 â‰¤ (âˆ‘ i : Fin 3, |L (Pi.single i 1)|) :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)

    have : (âˆ‘ i : Fin 3, |L (Pi.single i 1)|) â‰¤ â€–Lâ€– * â€–vâ€– := by
      calc
        (âˆ‘ i : Fin 3, |L (Pi.single i 1)|) = |L v| := by
          simpa [hv_eval, abs_of_nonneg hsum_nonneg]
        _ = â€–L vâ€– := by simp [Real.norm_eq_abs]
        _ â‰¤ â€–Lâ€– * â€–vâ€– := by simpa using (L.le_opNorm v)

    calc
      (âˆ‘ i : Fin 3, |L (Pi.single i 1)|) â‰¤ â€–Lâ€– * â€–vâ€– := this
      _ â‰¤ â€–Lâ€– * 1 := mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
      _ = â€–Lâ€– := by simp

  exact le_antisymm h_le1 h_le2
"""

text = re.sub(
    r"lemma opNorm_eq_sum_abs_fin3[\s\S]*?\n\n/-!\n# Elliptic Caccioppoli Inequality",
    new_opNorm + "\n\n/-!\n# Elliptic Caccioppoli Inequality",
    text,
    count=1,
)

p.write_text(text, encoding="utf-8")
print("fixed_helpers")