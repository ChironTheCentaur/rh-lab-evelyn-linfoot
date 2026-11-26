/-
Hardy's theorem (1914): the Riemann zeta function has infinitely many zeros on the critical line.

Proved here as a corollary of the zeta23 library (anthropics/zeta-23-lean), which proves that for
every ε > 0 and all large T at least (2/3 − ε) of the nontrivial zeros with 0 < Im ρ ≤ T lie on the
critical line (`Zeta23.thmA₀_cumulative`), that the same holds for simple zeros on the line
(`Zeta23.thmB₀_mult_cumulative`), and, from its unconditional Riemann–von Mangoldt formula, that
the number of nontrivial zeros with 0 < Im ρ ≤ T tends to infinity (`Zeta23.tendsto_Ncount_zero_atTop`).

If only finitely many zeros lay on the line, N₀*(0,T) would stay bounded, so (1/3)·N(0,T) would stay
bounded, contradicting N(0,T) → ∞.

The statements below mention only Mathlib's `riemannZeta`, `Complex.re` and `analyticOrderAt`.
-/
import Zeta23.Unconditional
import Zeta23.FinalMult
import Zeta23.Main

open Filter

namespace LeanClassics

/-- A subset of a finite set has at most its cardinality. Bounds N₀*(0,T) and N₀ˢ(0,T). -/
private lemma ncard_le_of_subset_finite {S A : Set ℂ} (hS : S.Finite) (hA : A ⊆ S) :
    A.ncard ≤ S.ncard :=
  Set.ncard_le_ncard hA hS

/-- Core argument: a count bounded below by (1/3)·N(0,T) for large T must be unbounded. -/
private lemma unbounded_of_third
    (f : ℝ → ℕ) (hf : ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - 1 / 3) * (Zeta23.Ncount 0 T : ℝ) ≤ f T)
    (K : ℕ) (hK : ∀ T, f T ≤ K) : False := by
  obtain ⟨T₀, hT₀⟩ := hf
  have htend := Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.riemannVonMangoldt_zeta
  obtain ⟨T, hT⟩ := (htend.eventually_gt_atTop (3 * (K : ℝ))).and (eventually_ge_atTop T₀)
    |>.exists
  have h1 := hT₀ T hT.2
  have h2 : (f T : ℝ) ≤ K := by exact_mod_cast hK T
  linarith [hT.1]

/-- **Hardy's theorem.** The Riemann zeta function has infinitely many zeros on the critical line
`Re s = 1/2`. -/
theorem riemannZeta_zeros_on_critical_line_infinite :
    {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2}.Infinite := by
  intro hfin
  refine unbounded_of_third (fun T => Zeta23.N0star 0 T) ?_
    {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2}.ncard (fun T => ?_)
  · obtain ⟨T₀, h⟩ := Zeta23.thmA₀_cumulative (1 / 3) (by norm_num)
    exact ⟨T₀, h⟩
  · refine ncard_le_of_subset_finite hfin ?_
    rintro ρ ⟨⟨⟨hz, -, -⟩, -, -⟩, hre⟩
    exact ⟨hz, hre⟩

/-- **Hardy's theorem for simple zeros.** Infinitely many zeros of the Riemann zeta function on the
critical line are simple (analytic order exactly one). -/
theorem riemannZeta_simple_zeros_on_critical_line_infinite :
    {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1}.Infinite := by
  intro hfin
  refine unbounded_of_third (fun T => Zeta23.N0simple 0 T) ?_
    {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1}.ncard
    (fun T => ?_)
  · obtain ⟨T₀, h⟩ := Zeta23.thmB₀_mult_cumulative (1 / 3) (by norm_num)
    exact ⟨T₀, h⟩
  · refine ncard_le_of_subset_finite hfin ?_
    rintro ρ ⟨⟨⟨⟨hz, -, -⟩, -, -⟩, hre⟩, hm⟩
    refine ⟨hz, hre, ?_⟩
    have hm' : (analyticOrderAt riemannZeta ρ).toNat = 1 := hm
    exact (ENat.toNat_eq_iff one_ne_zero).mp hm'

end LeanClassics
