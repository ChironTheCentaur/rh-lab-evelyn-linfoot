import EvelynLinfootFC.Main

/-!
# formal-conjectures `Erdos969.erdos_969.variants.evelyn_linfoot`, proved

The statement below is formal-conjectures' (`FormalConjectures/ErdosProblems/969.lean`, commit
`ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`, `@[category research solved, AMS 11]`, proof `sorry` there), token for
token; `controls/evelyn_linfoot_fc_fidelity.py` checks it. The proof is `EvelynLinfootFC.not_isLittleO`.
-/

namespace Erdos969

open Filter Asymptotics

/-- Evelyn and Linfoot proved $E(x)=\Omega(x^{1/4})$. -/
theorem erdos_969.variants.evelyn_linfoot :
    ¬(fun x => |squarefreeCountingError x|) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)) := by
  exact EvelynLinfootFC.not_isLittleO

end Erdos969
