/-
ζ has no zeros on the real segment (0, 1): in fact Re ζ(σ) ≤ 1 − 1/(1 − σ) < 0 there.

From the Euler–Maclaurin form (`riemannZeta0` with N = 1, PrimeNumberTheoremAnd as vendored in zeta23):
  ζ(s) = 1 − 1/(1 − s) − 1/2 + s ∫_1^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx   (Re s > 0, s ≠ 1),
and |⌊x⌋ + 1/2 − x| ≤ 1/2 bounds the last term by σ · (1/2) · (1/σ) = 1/2 at s = σ.
-/
import Zeta23.FromPNTPlus.ZetaBounds

open Complex MeasureTheory Set

namespace LeanClassics.RealZeros

lemma frac_bound (x : ℝ) : ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ))‖ ≤ 1 / 2 := by
  have e : ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  constructor <;> linarith

lemma integral_term_bound {σ : ℝ} (h0 : 0 < σ) :
    ‖(σ : ℂ) * ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖ ≤ 1 / 2 := by
  have ha : -σ - 1 < -1 := by linarith
  have hint : ∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) = 1 / σ := by
    rw [integral_Ioi_rpow_of_lt ha one_pos]
    simp
  have hbound : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖ ≤ 1 / 2 * x ^ (-σ - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have : (-((σ : ℂ) + 1)).re = -σ - 1 := by simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (frac_bound x) (Real.rpow_nonneg hx0.le _)
  have hI := norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt ha one_pos).const_mul (1 / 2)) hbound
  rw [integral_const_mul, hint] at hI
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
  calc σ * ‖∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖
      ≤ σ * (1 / 2 * (1 / σ)) := mul_le_mul_of_nonneg_left hI h0.le
    _ = 1 / 2 := by field_simp

/-- **ζ is negative on (0, 1)**, in the sense Re ζ(σ) ≤ 1 − 1/(1 − σ) < 0; in particular ζ has no
zeros on the real segment (0, 1). -/
theorem riemannZeta_re_neg_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).re < 0 := by
  have hne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← Zeta0EqZeta (N := 1) one_pos (by simpa using h0) hne, riemannZeta0_apply]
  have hb := integral_term_bound h0
  set J := (σ : ℂ) * ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((σ : ℂ) + 1))
  have hJ : J.re ≤ 1 / 2 := (Complex.re_le_norm J).trans hb
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hsum : (∑ n ∈ Finset.range (1 + 1), 1 / (n : ℂ) ^ (σ : ℂ)) = 1 := by
    simp [Finset.sum_range_succ, Complex.zero_cpow hσ0]
  have h1s : ((-(1 : ℕ) ^ (1 - (σ : ℂ))) / (1 - σ) + (-(1 : ℕ) ^ (-(σ : ℂ))) / 2 + J).re
      = -1 / (1 - σ) - 1 / 2 + J.re := by
    have e : (1 : ℂ) - σ = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
    simp only [Nat.cast_one, Complex.one_cpow]
    rw [e, Complex.add_re, Complex.add_re, Complex.div_ofReal_re]
    simp
    ring
  have hJ' : ((σ : ℂ) * ∫ x in Ioi ((1 : ℕ) : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((σ : ℂ) + 1)))
      = J := by simp [J]
  rw [hsum, hJ', Complex.add_re, h1s, Complex.one_re]
  have hlt : 1 < 1 / (1 - σ) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have : -1 / (1 - σ) = -(1 / (1 - σ)) := by ring
  linarith

/-- No zeros of ζ on the real segment (0, 1). -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := fun h => by
  have := riemannZeta_re_neg_of_mem_Ioo h0 h1
  rw [h] at this; simp at this

end LeanClassics.RealZeros
