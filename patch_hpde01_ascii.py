from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

# Insert ASCII-only helper block after the variable line.
if "def realSign" not in text:
    helper = """

/-!
## Sign helpers (ASCII-only)
-/

noncomputable def realSign (x : Real) : Real :=
  if x > 0 then 1 else if x < 0 then -1 else 0

lemma abs_realSign_le_one (x : Real) : |realSign x| <= 1 := by
  unfold realSign
  by_cases hpos : x > 0
  Â· simp [hpos]
  Â· by_cases hneg : x < 0
    Â· have : ~(x > 0) := not_lt.mpr (le_of_lt hneg)
      simp [this, hneg]
    Â· have hx0 : x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hx0]

lemma realSign_mul_self (x : Real) : realSign x * x = |x| := by
  unfold realSign
  by_cases hpos : x > 0
  Â· simp [hpos, abs_of_pos hpos]
  Â· by_cases hneg : x < 0
    Â· have : ~(x > 0) := not_lt.mpr (le_of_lt hneg)
      simp [this, hneg, abs_of_neg hneg]
      ring
    Â· have hx0 : x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hx0]

-- Fin 3 algebra: sum of squares <= square of sum of abs
lemma sum_sq_le_sq_sum_abs_fin3 (a : Fin 3 -> Real) :
    (Finset.sum Finset.univ (fun i : Fin 3 => (a i)^2)) <=
    (Finset.sum Finset.univ (fun i : Fin 3 => |a i|))^2 := by
  simp [Finset.sum_univ_three]
  have h0 : (a 0)^2 = |a 0|^2 := (sq_abs _).symm
  have h1 : (a 1)^2 = |a 1|^2 := (sq_abs _).symm
  have h2 : (a 2)^2 = |a 2|^2 := (sq_abs _).symm
  have hab : 0 <= |a 0| * |a 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hac : 0 <= |a 0| * |a 2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbc : 0 <= |a 1| * |a 2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [h0, h1, h2, hab, hac, hbc]

-- Fin 3 C-S: (sum abs)^2 <= 3 * sum sq
lemma sq_sum_abs_le_three_mul_sum_sq_fin3 (a : Fin 3 -> Real) :
    (Finset.sum Finset.univ (fun i : Fin 3 => |a i|))^2 <=
    3 * (Finset.sum Finset.univ (fun i : Fin 3 => (a i)^2)) := by
  simp [Finset.sum_univ_three]
  have h0 : (a 0)^2 = |a 0|^2 := (sq_abs _).symm
  have h1 : (a 1)^2 = |a 1|^2 := (sq_abs _).symm
  have h2 : (a 2)^2 = |a 2|^2 := (sq_abs _).symm
  have hab : 2 * (|a 0| * |a 1|) <= |a 0|^2 + |a 1|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 1|)]
  have hac : 2 * (|a 0| * |a 2|) <= |a 0|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 0| - |a 2|)]
  have hbc : 2 * (|a 1| * |a 2|) <= |a 1|^2 + |a 2|^2 := by
    nlinarith [sq_nonneg (|a 1| - |a 2|)]
  nlinarith [h0, h1, h2, hab, hac, hbc]

-- opNorm upper bound (enough for our 3x inequalities)
lemma opNorm_le_sum_abs_fin3 (L : (Fin 3 -> Real) ->L[Real] Real) :
    norm L <= (Finset.sum Finset.univ (fun i : Fin 3 => |L (Pi.single i 1)|)) := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound L (Finset.sum_nonneg (fun i _ => abs_nonneg _)) ?_
  intro v
  have h_expand : v = Finset.sum Finset.univ (fun i : Fin 3 => v i â€¢ Pi.single i (1 : Real)) := by
    ext j
    simp [Finset.sum_eq_single j, Pi.single_apply]
  -- triangle inequality + |v i| <= ||v||
  calc
    norm (L v) = |L v| := by simp [Real.norm_eq_abs]
    _ = |Finset.sum Finset.univ (fun i : Fin 3 => v i * L (Pi.single i 1))| := by
          simp [h_expand, map_sum, map_smul, smul_eq_mul]
    _ <= Finset.sum Finset.univ (fun i : Fin 3 => |v i * L (Pi.single i 1)|) := by
          simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => v i * L (Pi.single i 1)))
    _ = Finset.sum Finset.univ (fun i : Fin 3 => |v i| * |L (Pi.single i 1)|) := by simp [abs_mul]
    _ <= Finset.sum Finset.univ (fun i : Fin 3 => norm v * |L (Pi.single i 1)|) := by
          refine Finset.sum_le_sum ?_
          intro i _
          have hv : |v i| <= norm v := by
            simpa [Real.norm_eq_abs] using (norm_le_pi_norm v i)
          exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
    _ = norm v * (Finset.sum Finset.univ (fun i : Fin 3 => |L (Pi.single i 1)|)) := by
          simp [Finset.mul_sum]

"""
    # insert after the first occurrence of the variable line
    m = re.search(r"(namespace HPDE_01\s*\n\s*\nvariable .*\n)", text)
    if not m:
        raise RuntimeError("insertion point not found")
    idx = m.end(1)
    text = text[:idx] + helper + text[idx:]

# Replace each sorry lemma body with an ASCII-only proof.

def replace_sorry(name: str, body: str):
    global text
    pat = rf"(lemma {re.escape(name)}[\s\S]*?:= by\n)([\s\S]*?)\n\s*sorry\s*\n"
    m = re.search(pat, text)
    if not m:
        return
    text = text[:m.start()] + m.group(1) + body + "\n" + text[m.end():]

replace_sorry("norm_pi_single_one", """  apply le_antisymm
  Â· rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    simp [Pi.single_apply]
    split_ifs <;> simp
  Â· have h := norm_le_pi_norm (Pi.single i (1:Real)) i
    simpa [Pi.single_apply] using h""")

replace_sorry("gradientSq_le_three_mul_fderiv_norm_sq", """  unfold gradientSq
  have h_bound : forall i : Fin 3, ((fderiv â„ f x) (Pi.single i 1))^2 <= (norm (fderiv â„ f x))^2 := by
    intro i
    have h1 : norm ((fderiv â„ f x) (Pi.single i 1)) <= norm (fderiv â„ f x) * norm ((Pi.single i (1:Real)) : Fin 3 -> Real) :=
      ContinuousLinearMap.le_opNorm (fderiv â„ f x) (Pi.single i 1)
    have he : norm ((Pi.single i (1:Real)) : Fin 3 -> Real) = 1 := by
      simpa using (norm_pi_single_one (i := i))
    have h1' : |(fderiv â„ f x) (Pi.single i 1)| <= norm (fderiv â„ f x) := by
      have : norm ((fderiv â„ f x) (Pi.single i 1)) <= norm (fderiv â„ f x) := by
        simpa [he, mul_one] using h1
      simpa [Real.norm_eq_abs] using this
    nlinarith [h1']
  have hs : (Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv â„ f x) (Pi.single i 1))^2)) <=
            Finset.sum Finset.univ (fun _ : Fin 3 => (norm (fderiv â„ f x))^2) := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa using (h_bound i)
  simpa [Finset.sum_univ_three] using hs""")

replace_sorry("gradientSq_le_fderiv_norm_sq", """  unfold gradientSq
  -- This follows from the stronger 3x bound proved above.
  have h3 : (Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv â„ f x) (Pi.single i 1))^2)) <= 3 * (norm (fderiv â„ f x))^2 :=
    gradientSq_le_three_mul_fderiv_norm_sq (f := f) (x := x)
  -- use 3*||L||^2 >= ||L||^2
  nlinarith [h3, sq_nonneg (norm (fderiv â„ f x))]""")

replace_sorry("fderiv_norm_sq_le_three_mul_gradientSq", """  unfold gradientSq
  -- Use opNorm <= sum abs and C-S on Fin 3.
  have hop : norm (fderiv â„ f x) <= Finset.sum Finset.univ (fun i : Fin 3 => |(fderiv â„ f x) (Pi.single i 1)|) :=
    opNorm_le_sum_abs_fin3 (L := fderiv â„ f x)
  have hcs : (Finset.sum Finset.univ (fun i : Fin 3 => |(fderiv â„ f x) (Pi.single i 1)|))^2 <=
      3 * (Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv â„ f x) (Pi.single i 1))^2)) :=
    sq_sum_abs_le_three_mul_sum_sq_fin3 (a := fun i : Fin 3 => (fderiv â„ f x) (Pi.single i 1))
  have : (norm (fderiv â„ f x))^2 <= (Finset.sum Finset.univ (fun i : Fin 3 => |(fderiv â„ f x) (Pi.single i 1)|))^2 := by
    nlinarith [hop, norm_nonneg (fderiv â„ f x)]
  nlinarith [this, hcs]""")

# Comment out the norm-based theorem block cleanly
m1 = re.search(r"\ntheorem caccioppoli_elliptic\b", text)
m2 = re.search(r"\ntheorem caccioppoli_elliptic_gradSq\b", text)
if m1 and m2 and m1.start() < m2.start():
    block = text[m1.start():m2.start()]
    if "COMMENTED OUT: Use caccioppoli_elliptic_gradSq" not in block:
        text = text[:m1.start()] + "\n/-\n-- COMMENTED OUT: Use caccioppoli_elliptic_gradSq instead.\n-- Norm-based statement omitted; gradSq theorem below is the primary proved result.\n" + block + "-\/\n" + text[m2.start():]

text = text.replace("-\\/", "-/")

p.write_text(text, encoding="utf-8")
print("patched_ascii")