import EvelynLinfootFC
/-! PLANTED CONTROL: each of these must fail to compile (lines 7, 11, 15); the true restatement must pass. -/
open Erdos969 Filter Asymptotics

-- exponent 1/2 instead of 1/4 (false by the PNT, so the proof must not transfer)
theorem plant1 : ¬(fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 2 : ℝ)) :=
  erdos_969.variants.evelyn_linfoot

-- O instead of o (the negated O-statement is false: E = O(x))
theorem plant2 : ¬(fun x => |squarefreeCountingError x|) =O[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)) :=
  erdos_969.variants.evelyn_linfoot

-- un-negated (claims E = o(x^{1/4}))
theorem plant3 : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)) :=
  erdos_969.variants.evelyn_linfoot

theorem true_restated :
    ¬(fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)) :=
  erdos_969.variants.evelyn_linfoot
