import Mathlib

/-!
# formal-conjectures' definitions for Erdős Problem 969, copied verbatim

From google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/969.lean`, commit
`ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8` (Copyright 2026 The Formal Conjectures Authors, Apache-2.0).
formal-conjectures is on another toolchain and cannot be imported, so the definitions are copied; the copy is checked
token for token by `controls/evelyn_linfoot_fc_fidelity.py`. Only the module-system lines (`module`,
`public import FormalConjecturesUtil`, `@[expose] public section`) and FC's `category`/`AMS` attributes are left out.
-/

namespace Erdos969

open Filter Asymptotics

/-- The squarefree counting function `Q(x)`. -/
def squarefreeCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter Squarefree).card

/-- Exactly seven integers in $[1,10]$ are squarefree, including $1$. -/
theorem squarefreeCounting_ten : squarefreeCounting 10 = 7 := by
  decide +kernel

/-- The error term in `Q(x) = (6 / π^2) x + E(x)`. -/
noncomputable def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x

end Erdos969
