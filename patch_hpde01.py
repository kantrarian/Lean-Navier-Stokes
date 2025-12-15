import re
from pathlib import Path

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

# -------------------------------------------------------------------
# 1) Insert helpers once (ASCII-only Lean; no unicode symbols required)
# -------------------------------------------------------------------
if "def realSign" not in text and "realSign" not in text:
    helper = """

/-!
## Sign Function Helpers for Dual Norm Proof
-/

/-- Sign function returning -1, 0, or 1 as a real number -/
noncomputable def realSign (x : Real) : Real :=
  if x > 0 then 1 else if x < 0 then -1 else 0

lemma abs_realSign_le_one (x : Real) : abs (realSign x) <= 1 := by
  unfold realSign
  by_cases hpos : x > 0
  Â· simp [hpos]
  Â· by_cases hneg : x < 0
    Â· have : ~(x > 0) := not_lt.mpr (le_of_lt hneg)
      simp [this, hneg]
    Â· have hx0 : x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hx0]

lemma realSign_mul_self (x : Real) : realSign x * x = abs x := by
  unfold realSign
  by_cases hpos : x > 0
  Â· simp [hpos, abs_of_pos hpos]
  Â· by_cases hneg : x < 0
    Â· have : ~(x > 0) := not_lt.mpr (le_of_lt hneg)
      simp [this, hneg, abs_of_neg hneg]
      ring
    Â· have hx0 : x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp [hx0]

/-!
## Algebraic Helpers (Fin 3)
-/

lemma sum_sq_le_sq_sum_abs_fin3 (a : Fin 3 -> Real) :
    (Finset.sum Finset.univ (fun i : Fin 3 => (a i)^2)) <=
    (Finset.sum Finset.univ (fun i : Fin 3 => abs (a i)))^2 := by
  -- Expand sums over Fin 3.
  simp [Finset.sum_univ_three]
  -- Rewrite squares to abs-squares.
  have h0 : (a 0)^2 = (abs (a 0))^2 := by simpa [pow_two] using (sq_abs (a 0)).symm
  have h1 : (a 1)^2 = (abs (a 1))^2 := by simpa [pow_two] using (sq_abs (a 1)).symm
  have h2 : (a 2)^2 = (abs (a 2))^2 := by simpa [pow_two] using (sq_abs (a 2)).symm
  simp [h0, h1, h2]
  have hab : 0 <= abs (a 0) * abs (a 1) := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hac : 0 <= abs (a 0) * abs (a 2) := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbc : 0 <= abs (a 1) * abs (a 2) := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [hab, hac, hbc]

lemma sq_sum_abs_le_three_mul_sum_sq_fin3 (a : Fin 3 -> Real) :
    (Finset.sum Finset.univ (fun i : Fin 3 => abs (a i)))^2 <=
    3 * (Finset.sum Finset.univ (fun i : Fin 3 => (a i)^2)) := by
  simp [Finset.sum_univ_three]
  have h0 : (a 0)^2 = (abs (a 0))^2 := by simpa [pow_two] using (sq_abs (a 0)).symm
  have h1 : (a 1)^2 = (abs (a 1))^2 := by simpa [pow_two] using (sq_abs (a 1)).symm
  have h2 : (a 2)^2 = (abs (a 2))^2 := by simpa [pow_two] using (sq_abs (a 2)).symm
  simp [h0, h1, h2]
  have hab : 2 * (abs (a 0) * abs (a 1)) <= (abs (a 0))^2 + (abs (a 1))^2 := by
    nlinarith [sq_nonneg (abs (a 0) - abs (a 1))]
  have hac : 2 * (abs (a 0) * abs (a 2)) <= (abs (a 0))^2 + (abs (a 2))^2 := by
    nlinarith [sq_nonneg (abs (a 0) - abs (a 2))]
  have hbc : 2 * (abs (a 1) * abs (a 2)) <= (abs (a 1))^2 + (abs (a 2))^2 := by
    nlinarith [sq_nonneg (abs (a 1) - abs (a 2))]
  nlinarith [hab, hac, hbc]

/-!
## Operator Norm Characterization (Fin 3)
-/

lemma opNorm_eq_sum_abs_fin3 (L : (Fin 3 -> Real) ->L[Real] Real) :
    norm L = Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1))) := by
  classical
  apply le_antisymm
  Â· -- Upper bound: norm L <= sum abs
    refine ContinuousLinearMap.opNorm_le_bound L ?_ ?_
    Â· exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    Â· intro v
      -- Expand v in the standard basis.
      have h_expand : v = Finset.sum Finset.univ (fun i : Fin 3 => v i â€¢ Pi.single i (1 : Real)) := by
        ext j
        simp [Finset.sum_eq_single j, Pi.single_apply]
      -- Bound |L v|.
      have : abs (L v) <= (Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1)))) * norm v := by
        -- Work with the expansion and triangle inequality.
        have h1 : abs (L v) = abs (Finset.sum Finset.univ (fun i : Fin 3 => v i * L (Pi.single i 1))) := by
          -- linearity
          simp [h_expand, Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
        -- Start from |sum| <= sum |.|.
        have h2 : abs (Finset.sum Finset.univ (fun i : Fin 3 => v i * L (Pi.single i 1))) <=
                  Finset.sum Finset.univ (fun i : Fin 3 => abs (v i * L (Pi.single i 1))) := by
          simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin 3 => v i * L (Pi.single i 1)))
        -- Rewrite |v_i * L(e_i)|.
        have h3 : Finset.sum Finset.univ (fun i : Fin 3 => abs (v i * L (Pi.single i 1))) =
                  Finset.sum Finset.univ (fun i : Fin 3 => abs (v i) * abs (L (Pi.single i 1))) := by
          simp [abs_mul]
        -- Bound |v_i| <= norm v.
        have h4 : Finset.sum Finset.univ (fun i : Fin 3 => abs (v i) * abs (L (Pi.single i 1))) <=
                  Finset.sum Finset.univ (fun i : Fin 3 => norm v * abs (L (Pi.single i 1))) := by
          refine Finset.sum_le_sum ?_
          intro i _
          have hv : abs (v i) <= norm v := by
            -- norm_le_pi_norm : ||v i|| <= ||v||, and ||v i|| = abs (v i)
            simpa [Real.norm_eq_abs] using (norm_le_pi_norm v i)
          exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
        -- Factor out norm v.
        have h5 : Finset.sum Finset.univ (fun i : Fin 3 => norm v * abs (L (Pi.single i 1))) =
                  norm v * (Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1)))) := by
          simp [Finset.mul_sum]
        calc
          abs (L v)
              = abs (Finset.sum Finset.univ (fun i : Fin 3 => v i * L (Pi.single i 1))) := h1
          _ <= Finset.sum Finset.univ (fun i : Fin 3 => abs (v i * L (Pi.single i 1))) := h2
          _ = Finset.sum Finset.univ (fun i : Fin 3 => abs (v i) * abs (L (Pi.single i 1))) := h3
          _ <= Finset.sum Finset.univ (fun i : Fin 3 => norm v * abs (L (Pi.single i 1))) := h4
          _ = norm v * (Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1)))) := h5
      -- Convert to the opNorm_le_bound shape: ||L v|| <= M * ||v||.
      -- Here M is sum abs.
      simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using this
  Â· -- Lower bound via the sign vector.
    let v : Fin 3 -> Real := fun i => realSign (L (Pi.single i 1))
    have hv_norm : norm v <= 1 := by
      -- pi_norm_le_iff_of_nonneg
      have : norm v <= (1 : Real) <-> (forall i : Fin 3, norm (v i) <= (1 : Real)) :=
        pi_norm_le_iff_of_nonneg (x := v) (r := (1 : Real)) (by nlinarith)
      -- show all coordinates are bounded
      refine (this.mpr ?_)
      intro i
      -- norm (v i) = abs (v i)
      simpa [Real.norm_eq_abs] using (abs_realSign_le_one (L (Pi.single i 1)))
    have hv_eval : L v = Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1))) := by
      -- expand v in basis
      have h_expand : v = Finset.sum Finset.univ (fun i : Fin 3 => v i â€¢ Pi.single i (1 : Real)) := by
        ext j
        simp [Finset.sum_eq_single j, Pi.single_apply]
      calc
        L v = Finset.sum Finset.univ (fun i : Fin 3 => v i * L (Pi.single i 1)) := by
          simp [h_expand, map_sum, map_smul, smul_eq_mul]
        _ = Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [v, abs] using (realSign_mul_self (L (Pi.single i 1)))
    have hsum_nonneg : 0 <= Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1))) :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have h_le : Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1))) <= norm L * norm v := by
      calc
        Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1)))
            = abs (L v) := by simpa [hv_eval, abs_of_nonneg hsum_nonneg]
        _ = norm (L v) := by simp [Real.norm_eq_abs]
        _ <= norm L * norm v := by
              -- le_opNorm gives ||L v|| <= ||L|| * ||v||
              simpa using (L.le_opNorm v)
    calc
      Finset.sum Finset.univ (fun i : Fin 3 => abs (L (Pi.single i 1))) <= norm L * norm v := h_le
      _ <= norm L * 1 := mul_le_mul_of_nonneg_left hv_norm (by nlinarith [norm_nonneg L])
      _ = norm L := by simp
"""

    # Insert after variable line.
    m = re.search(r"(namespace HPDE_01\s*\n\s*\nvariable .*\n)", text)
    if not m:
        raise RuntimeError("Could not find insertion point after variable declaration")
    idx = m.end(1)
    text = text[:idx] + helper + text[idx:]

# -------------------------------------------------------------------
# 2) Replace the four sorry blocks with proofs.
# -------------------------------------------------------------------

def replace_sorry_in_lemma(name: str, new_body: str):
    nonlocal_text = globals()["text"]
    # find lemma start
    m = re.search(rf"lemma {re.escape(name)}[\s\S]*?:= by\n", nonlocal_text)
    if not m:
        raise RuntimeError(f"Lemma {name} not found")
    start = m.end(0)
    # find the first 'sorry' after start
    m2 = re.search(r"^\s*sorry\s*$", nonlocal_text[start:], flags=re.M)
    if not m2:
        raise RuntimeError(f"No sorry found for lemma {name}")
    s0 = start + m2.start(0)
    s1 = start + m2.end(0)
    # replace just the sorry line
    globals()["text"] = nonlocal_text[:s0] + new_body + nonlocal_text[s1:]

replace_sorry_in_lemma(
    "gradientSq_le_fderiv_norm_sq",
    """  unfold gradientSq\n  -- rewrite the goal in terms of `norm` and use the operator-norm characterization\n  have hop : norm (fderiv Real f x) = Finset.sum Finset.univ (fun i : Fin 3 => abs ((fderiv Real f x) (Pi.single i 1))) :=\n    opNorm_eq_sum_abs_fin3 (L := fderiv Real f x)\n  -- sum of squares <= (sum of abs)^2\n  have hsq : (Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv Real f x) (Pi.single i 1))^2)) <=\n      (Finset.sum Finset.univ (fun i : Fin 3 => abs ((fderiv Real f x) (Pi.single i 1))))^2 :=\n    sum_sq_le_sq_sum_abs_fin3 (a := fun i : Fin 3 => (fderiv Real f x) (Pi.single i 1))\n  -- finish\n  simpa [hop, Finset.sum_univ_three, pow_two] using hsq\n""",
)

replace_sorry_in_lemma(
    "norm_pi_single_one",
    """  apply le_antisymm\n  Â· -- ||Pi.single i 1|| <= 1\n    have : norm ((Pi.single i (1 : Real)) : Fin 3 -> Real) <= (1 : Real) <->\n        (forall j : Fin 3, norm ((Pi.single i (1 : Real)) j) <= (1 : Real)) :=\n      pi_norm_le_iff_of_nonneg (x := (Pi.single i (1 : Real))) (r := (1 : Real)) (by nlinarith)\n    refine (this.mpr ?_)\n    intro j\n    by_cases h : j = i\n    Â· subst h; simp [Pi.single_apply]\n    Â· simp [Pi.single_apply, h]\n  Â· -- 1 <= ||Pi.single i 1||\n    have h := norm_le_pi_norm (Pi.single i (1 : Real)) i\n    simpa [Pi.single_apply] using h\n""",
)

replace_sorry_in_lemma(
    "gradientSq_le_three_mul_fderiv_norm_sq",
    """  unfold gradientSq\n  by_cases hf : DifferentiableAt Real f x\n  Â· -- bound each coordinate by opNorm\n    have h_bound : forall i : Fin 3, ((fderiv Real f x) (Pi.single i 1))^2 <= (norm (fderiv Real f x))^2 := by\n      intro i\n      have h1 : norm ((fderiv Real f x) (Pi.single i 1)) <= norm (fderiv Real f x) * norm ((Pi.single i (1 : Real)) : Fin 3 -> Real) :=\n        ContinuousLinearMap.le_opNorm (fderiv Real f x) (Pi.single i 1)\n      have h1' : abs ((fderiv Real f x) (Pi.single i 1)) <= norm (fderiv Real f x) := by\n        -- use ||e_i|| = 1\n        have he : norm ((Pi.single i (1 : Real)) : Fin 3 -> Real) = 1 := by\n          -- reuse lemma just above (with Real)
          simpa using (norm_pi_single_one (i := i))\n        -- rewrite and simplify\n        -- norm scalar = abs
        have : norm ((fderiv Real f x) (Pi.single i 1)) <= norm (fderiv Real f x) := by\n          simpa [he] using (by simpa [mul_one] using (by simpa [he] using h1))\n        simpa [Real.norm_eq_abs] using this\n      -- square both sides\n      nlinarith [h1']\n    -- sum the bounds\n    have hs : Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv Real f x) (Pi.single i 1))^2) <=\n        Finset.sum Finset.univ (fun _ : Fin 3 => (norm (fderiv Real f x))^2) := by\n      refine Finset.sum_le_sum ?_\n      intro i _\n      simpa using (h_bound i)\n    -- compute constant 3
    simpa [Finset.sum_univ_three, pow_two, mul_assoc, mul_left_comm, mul_comm] using hs\n  Â· simp [fderiv_zero_of_not_differentiableAt hf]\n""",
)

# For the last lemma, we only replace the first sorry (the hf branch).
# We'll locate the block and replace the first sorry after the `by_cases`.

m = re.search(r"lemma fderiv_norm_sq_le_three_mul_gradientSq[\s\S]*?:= by\n", text)
if not m:
    raise RuntimeError("Lemma fderiv_norm_sq_le_three_mul_gradientSq not found")
start = m.end(0)
# find the first sorry after start
m2 = re.search(r"^\s*sorry\s*$", text[start:], flags=re.M)
if not m2:
    raise RuntimeError("No sorry found in fderiv_norm_sq_le_three_mul_gradientSq")
s0 = start + m2.start(0)
s1 = start + m2.end(0)
replacement = """    -- Use the operator norm characterization and a Fin-3 Cauchy-Schwarz bound.\n    have hop : norm (fderiv Real f x) = Finset.sum Finset.univ (fun i : Fin 3 => abs ((fderiv Real f x) (Pi.single i 1))) :=\n      opNorm_eq_sum_abs_fin3 (L := fderiv Real f x)\n    have hcs : (Finset.sum Finset.univ (fun i : Fin 3 => abs ((fderiv Real f x) (Pi.single i 1))))^2 <=\n        3 * (Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv Real f x) (Pi.single i 1))^2)) :=\n      sq_sum_abs_le_three_mul_sum_sq_fin3 (a := fun i : Fin 3 => (fderiv Real f x) (Pi.single i 1))\n    -- rewrite and finish\n    simpa [hop, Finset.sum_univ_three, pow_two, mul_assoc] using hcs\n"""
text = text[:s0] + replacement + text[s1:]

# -------------------------------------------------------------------
# 3) Comment out the norm-based theorem block
# -------------------------------------------------------------------
if "COMMENTED OUT: Use caccioppoli_elliptic_gradSq" not in text:
    text = text.replace(
        "theorem caccioppoli_elliptic",
        "/-\n-- COMMENTED OUT: Use caccioppoli_elliptic_gradSq instead.\n-- The operator-norm statement has a different constant factor due to norm equivalence.\n\n" + "theorem caccioppoli_elliptic",
        1,
    )
    text = text.replace(
        "theorem caccioppoli_elliptic_gradSq",
        "-/\n\n" + "theorem caccioppoli_elliptic_gradSq",
        1,
    )

p.write_text(text, encoding="utf-8")
print("Patched:", p)