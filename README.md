# The squarefree counting error is not o(x^{1/4}) (Evelyn–Linfoot 1931), in Lean 4

Author: Sky ([@ChironTheCentaur](https://github.com/ChironTheCentaur)). Standalone package, 2026-11-26.

> **AI disclosure.** The Lean proofs and this package were written with AI assistance (Claude, by Anthropic), under
> the author's direction. The result is listed only because the Lean kernel checks it here and `#print axioms`
> shows nothing beyond Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## The theorem

With Q(x) the number of squarefree n ≤ x and E(x) = Q(x) − (6/π²) x, Evelyn and Linfoot (1931) showed
E(x) = Ω(x^{1/4}).

```lean
theorem Erdos969.erdos_969.variants.evelyn_linfoot :
    ¬(fun x => |squarefreeCountingError x|) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ))
-- squarefreeCounting x = ((Finset.Icc 1 x).filter Squarefree).card
-- squarefreeCountingError x = (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x
```

The definitions and the statement are, token for token, those of google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/969.lean`, commit `ea8e3e19`, where the proof is `sorry`). formal-conjectures is on
another Lean toolchain, so they are copied (Apache-2.0, see `NOTICE`) and checked by
`controls/evelyn_linfoot_fc_fidelity.py`. No hypothesis: no RH, no zero computations.

Proof idea: if E(n) = o(n^{1/4}), the Mellin transform G(s) of E satisfies s G(s) = ζ(s)/ζ(2s) − (6/π²) ζ(s) and is
holomorphic on Re s > 1/4 with a growth bound there. Hardy's theorem (ζ has zeros on the critical line,
`LeanClassics.Hardy`) gives a zero ρ of ζ with Re ρ = 1/2, so ζ(2s) vanishes at s = ρ/2 with Re = 1/4, where the
bound on G contradicts the pole of ζ(s)/ζ(2s).

The mathematics is Evelyn and Linfoot's; the formal proof is ours.

## Other Lean work we know of (searched 2026-11-26)

| where | what it has |
|---|---|
| google-deepmind/formal-conjectures `ErdosProblems/969.lean` | the statement, proof `sorry`, no `formal_proof` link |
| GitHub code search for `evelyn_linfoot` and `erdos_969` (Lean, default branches) | only formal-conjectures' file |
| this package | formal-conjectures' exact statement, proved |

"None found" is a search result with those limits, not proof that nothing exists.

## What is in the package

The import closure of the result, 150 modules (48152 lines of Lean) under their original module names.
`Zeta23/` is a subset of Anthropic's zeta-23-lean (Apache-2.0, `LICENSE.zeta23`, `NOTICE.zeta23`), ported to Lean
v4.35.0. Only Mathlib (pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`) is fetched at build time. Source commit: `92b7cdc659d5b590a56638dd88b23fbea95add12`.

## Verify it

```
python3 check.py
```

It runs `lake exe cache get` and `lake build` (every module), then:

* `AxiomAudit.lean`: 9 `#print axioms` lines. PASS needs every one to report only standard axioms, and the
  set of reported names to equal the set listed.
* `PlantedSorry.lean`: a planted `sorry` that the audit must report as `sorryAx`, so the audit is shown able to fail.
* `controls/EvelynLinfootFCPlant.lean`: false variants of the statement that must fail at exactly lines 7, 11 and 15,
  beside the true statement, which must be accepted.
* `MANIFEST.sha256`: every checked file hashes to the shipped bytes.

It writes `CHECK_RESULT.json` and exits 0 only on PASS.

On Windows, clone with `git clone -c core.autocrlf=false ...` when checking a pinned older commit; `main` carries a .gitattributes that keeps exact bytes.

Statement fidelity against formal-conjectures itself (needs a clone of it):

```
git clone https://github.com/google-deepmind/formal-conjectures FC
git -C FC checkout ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8
python3 -I controls/evelyn_linfoot_fc_fidelity.py FC --self-test
```
