import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# LHF-01: Matrix commutator basics

This package previously had a corrupted (non-Lean) file. This file is a
compilable Lean baseline providing small algebraic commutator lemmas.

We avoid non-ASCII symbols in proofs/statements to prevent Windows encoding
corruption.
-/

open Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) Real

namespace LHF01

def commutator (A B : Mat3) : Mat3 := A * B - B * A

lemma commutator_antisymm (A B : Mat3) : commutator A B = - commutator B A := by
  ext i j
  simp [commutator, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma commutator_zero_iff_commute (A B : Mat3) : Iff (commutator A B = 0) (A * B = B * A) := by
  constructor
  case mp =>
    intro h
    have h' : A * B - B * A = 0 := by
      simpa [commutator] using h
    exact sub_eq_zero.mp h'
  case mpr =>
    intro h
    have h' : A * B - B * A = 0 := sub_eq_zero.mpr h
    simpa [commutator] using h'

lemma trace_commutator_zero (A B : Mat3) : Matrix.trace (commutator A B) = 0 := by
  have htr : Matrix.trace (A * B) = Matrix.trace (B * A) := by
    simpa using (Matrix.trace_mul_comm A B)
  -- trace is linear, so trace(AB - BA) = trace(AB) - trace(BA)
  calc
    Matrix.trace (commutator A B)
        = Matrix.trace (A * B) - Matrix.trace (B * A) := by
            simp [commutator, Matrix.trace_sub]
    _ = 0 := by
            simpa [htr]

end LHF01