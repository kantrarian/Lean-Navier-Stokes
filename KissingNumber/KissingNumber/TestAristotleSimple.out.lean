/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: be9a65d8-07c9-45e3-81b1-1e06408db08d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem test_simple : ∀ n : ℕ, n + 0 = n
-/

import Mathlib.Tactic


-- Simple test to verify Aristotle API works
theorem test_simple : ∀ n : ℕ, n + 0 = n := by
  -- The base case is when $n = 0$.
  simp [Nat.add_zero]