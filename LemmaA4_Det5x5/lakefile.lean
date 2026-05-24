import Lake
open Lake DSL

package LemmaA4_Det5x5 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "dc19f2a67ff55a2078ba23a4c1740a5eb0d50e41"

@[default_target]
lean_lib LemmaA4_Det5x5 where
  -- Strengthened Lemma A.4: explicit 5×5 determinant for joint surjectivity.
