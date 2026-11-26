import EvelynLinfootFC.Defs
import LeanClassics.SquarefreeLSeries

/-!
# The Mellin transform of the squarefree error term

`E(n) = Q(n) − (6/π²) n` (formal-conjectures' `squarefreeCountingError`), extended to `t > 1` as `E(⌊t⌋)` and by `0`
on `t ≤ 1` (`g`). `G s = ∫_1^∞ E(⌊t⌋) t^{−s−1} dt` (`G`, as Mathlib's `mellin g (−s)`).

* `mul_G_eq`: for `Re s > 1`, `s · G(s) = ζ(s)/ζ(2s) − (6/π²) ζ(s)` (Mathlib's `LSeries_eq_mul_integral` with the
  coefficients `μ(n)² − 6/π²`, and `LeanClassics.SquarefreeLSeries.LSeries_moebius_sq`).
* `differentiableAt_G`: if `E(n) = O(n^{1/4})` then `G` is complex differentiable on `Re s > 1/4`
  (Mathlib's `mellin_differentiableAt_of_isBigO_rpow`).
* `norm_G_le`: if `|E(⌊t⌋)| ≤ B + η t^{1/4}` for `t > 1`, then `‖G s‖ ≤ B/σ + η/(σ − 1/4)` for `σ = Re s > 1/4`.
* `exists_bound`: `E = o(n^{1/4})` gives such a `B` for every `η > 0`.
-/

open Complex Filter Asymptotics Topology MeasureTheory Set
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace EvelynLinfootFC

open Erdos969

lemma κ_pos : (0 : ℝ) < 6 / Real.pi ^ 2 := by positivity

/-- The squarefree indicator as `μ(n)²`. -/
def a : ℕ → ℂ := fun n => ((μ n ^ 2 : ℤ) : ℂ)

lemma a_eq (n : ℕ) : a n = if Squarefree n then 1 else 0 := by
  unfold a
  split_ifs with h
  · rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree h]; simp
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

lemma sum_a (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, a k = (squarefreeCounting n : ℂ) := by
  simp only [a_eq, squarefreeCounting]
  rw [Finset.sum_boole]

/-- The coefficients `μ(n)² − 6/π²`. -/
def f : ℕ → ℂ := a - ((6 / Real.pi ^ 2 : ℝ) : ℂ) • (1 : ℕ → ℂ)

lemma sum_f (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, f k = (squarefreeCountingError n : ℂ) := by
  simp only [f, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Finset.sum_sub_distrib,
    sum_a, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, squarefreeCountingError, add_tsub_cancel_right]
  push_cast
  ring

lemma squarefreeCounting_le (n : ℕ) : squarefreeCounting n ≤ n := by
  unfold squarefreeCounting
  calc _ ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma abs_E_le (n : ℕ) : |squarefreeCountingError n| ≤ (1 + 6 / Real.pi ^ 2) * n := by
  unfold squarefreeCountingError
  have h1 : (squarefreeCounting n : ℝ) ≤ n := by exact_mod_cast squarefreeCounting_le n
  have h0 : (0 : ℝ) ≤ squarefreeCounting n := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hk := κ_pos
  rw [abs_le]; constructor <;> nlinarith

/-! ### The Dirichlet series -/

lemma LSeries_a {s : ℂ} (hs : 1 < s.re) : LSeries a s = riemannZeta s / riemannZeta (2 * s) :=
  (LeanClassics.SquarefreeLSeries.LSeries_moebius_sq hs).1

lemma LSeriesSummable_a {s : ℂ} (hs : 1 < s.re) : LSeriesSummable a s :=
  (LeanClassics.SquarefreeLSeries.LSeries_moebius_sq hs).2

lemma LSeriesSummable_f {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s :=
  (LSeriesSummable_a hs).sub ((LSeriesSummable_one_iff.mpr hs).smul _)

lemma LSeries_f {s : ℂ} (hs : 1 < s.re) :
    LSeries f s = riemannZeta s / riemannZeta (2 * s) - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta s := by
  rw [f, LSeries_sub (LSeriesSummable_a hs) ((LSeriesSummable_one_iff.mpr hs).smul _), LSeries_smul,
    LSeries_one_eq_riemannZeta hs, LSeries_a hs]

lemma sum_f_isBigO :
    (fun n => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (1 + 6 / Real.pi ^ 2) (Eventually.of_forall fun n => ?_)
  rw [sum_f, Complex.norm_real, Real.rpow_one, Real.norm_natCast, Real.norm_eq_abs]
  exact abs_E_le n

/-! ### `g` and `G` -/

/-- `E(⌊t⌋)` on `t > 1`, `0` elsewhere. -/
def g : ℝ → ℂ := indicator (Ioi 1) fun t => ((squarefreeCountingError ⌊t⌋₊ : ℝ) : ℂ)

/-- `G(s) = ∫_1^∞ E(⌊t⌋) t^{−s−1} dt`. -/
def G (s : ℂ) : ℂ := mellin g (-s)

lemma G_eq (s : ℂ) :
    G s = ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  unfold G mellin
  have h1 : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • g t) =
      indicator (Ioi 1) (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem ht, smul_eq_mul, sum_f]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · simp [g, indicator_of_notMem ht]
  rw [h1, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

/-- `s · G(s) = ζ(s)/ζ(2s) − (6/π²) ζ(s)` for `Re s > 1`. -/
theorem mul_G_eq {s : ℂ} (hs : 1 < s.re) :
    s * G s = riemannZeta s / riemannZeta (2 * s) - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta s := by
  rw [← LSeries_f hs, LSeries_eq_mul_integral f zero_le_one hs (LSeriesSummable_f hs) sum_f_isBigO, G_eq]

/-! ### Bounds for `g` -/

lemma norm_g_le_lin (t : ℝ) : ‖g t‖ ≤ (1 + 6 / Real.pi ^ 2) * |t| := by
  have hk := κ_pos
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · simp only [g, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs]
    have ht1 : (1 : ℝ) < t := ht
    refine (abs_E_le _).trans ?_
    rw [abs_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) (by linarith)
  · simp only [g, indicator_of_notMem ht, norm_zero]; positivity

lemma measurable_g : Measurable g := by
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact (measurable_ofReal.comp (measurable_from_nat (f := squarefreeCountingError))).comp Nat.measurable_floor

lemma locallyIntegrableOn_g : LocallyIntegrableOn g (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k _ hk
  obtain ⟨R, hR⟩ := hk.isBounded.exists_norm_le
  refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne measurable_g.aestronglyMeasurable
    (M := (1 + 6 / Real.pi ^ 2) * R) ?_
  refine (ae_restrict_iff' hk.measurableSet).mpr (Eventually.of_forall fun t ht => ?_)
  refine (norm_g_le_lin t).trans (mul_le_mul_of_nonneg_left ?_ (by linarith [κ_pos]))
  have := hR t ht
  rwa [Real.norm_eq_abs] at this

/-- From `E = o(n^{1/4})`: for every `η > 0` some `B ≥ 0` with `‖g t‖ ≤ B + η t^{1/4}` on `t > 1`. -/
lemma exists_bound (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)))
    {η : ℝ} (hη : 0 < η) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 1 < t → ‖g t‖ ≤ B + η * t ^ (1 / 4 : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.def hη)
  refine ⟨∑ n ∈ Finset.range N, |squarefreeCountingError n|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht => ?_⟩
  have hmem : t ∈ Ioi (1 : ℝ) := ht
  simp only [g, indicator_of_mem hmem, Complex.norm_real, Real.norm_eq_abs]
  have hB : 0 ≤ ∑ n ∈ Finset.range N, |squarefreeCountingError n| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hη' : 0 ≤ η * t ^ (1 / 4 : ℝ) := mul_nonneg hη.le (Real.rpow_nonneg (by linarith) _)
  rcases lt_or_ge ⌊t⌋₊ N with hlt | hge
  · have := Finset.single_le_sum (f := fun n => |squarefreeCountingError n|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)
    linarith
  · have h1 := hN _ hge
    rw [Real.norm_eq_abs, abs_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h1
    have h2 : (⌊t⌋₊ : ℝ) ^ (1 / 4 : ℝ) ≤ t ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by norm_num)
    nlinarith

lemma g_isBigO_top (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ))) :
    g =O[atTop] fun t : ℝ => t ^ (-(-(1 / 4 : ℝ))) := by
  obtain ⟨B, hB, hb⟩ := exists_bound h one_pos
  refine IsBigO.of_bound (B + 1) ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [neg_neg, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have h1 : (1 : ℝ) ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow ht.le (by norm_num)
  have := hb t ht
  nlinarith

lemma g_isBigO_bot (b : ℝ) : g =O[𝓝[>] 0] fun t : ℝ => t ^ (-b) := by
  have h0 : g =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have : t ∉ Ioi (1 : ℝ) := fun h => by have := ht.2; simp only [mem_Ioi] at h; linarith
    simp [g, indicator_of_notMem this]
  exact h0.trans_isBigO (isBigO_zero _ _)

/-- Under `E = o(n^{1/4})`, `G` is complex differentiable on `Re s > 1/4`. -/
theorem differentiableAt_G
    (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)))
    {s : ℂ} (hs : 1 / 4 < s.re) : DifferentiableAt ℂ G s := by
  have hd : DifferentiableAt ℂ (mellin g) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 4)) (b := -s.re - 1) locallyIntegrableOn_g
      (g_isBigO_top h) (by rw [neg_re]; linarith) (g_isBigO_bot _) (by rw [neg_re]; linarith)
  exact hd.comp s differentiableAt_id.neg

/-- The bound `‖G s‖ ≤ B/σ + η/(σ − 1/4)`. -/
theorem norm_G_le {B η : ℝ}
    (hb : ∀ t : ℝ, 1 < t → ‖g t‖ ≤ B + η * t ^ (1 / 4 : ℝ)) {s : ℂ} (hs : 1 / 4 < s.re) :
    ‖G s‖ ≤ B / s.re + η / (s.re - 1 / 4) := by
  have hs0 : 0 < s.re := by linarith
  have e1 : (-s.re - 1) < -1 := by linarith
  have e2 : (1 / 4 - s.re - 1) < -1 := by linarith
  have i1 := integrableOn_Ioi_rpow_of_lt e1 zero_lt_one
  have i2 := integrableOn_Ioi_rpow_of_lt e2 zero_lt_one
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (-s.re - 1) + η * t ^ (1 / 4 - s.re - 1)) (Ioi 1) :=
    (i1.const_mul B).add (i2.const_mul η)
  unfold G mellin
  have h1 : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • g t) =
      indicator (Ioi 1) (fun t : ℝ => (t : ℂ) ^ (-s - 1) • g t) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht]; simp [g, indicator_of_notMem ht]
  rw [h1, setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, neg_re, one_re]
    have hp : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg ht0.le _
    have hsplit : t ^ (1 / 4 - s.re - 1) = t ^ (1 / 4 : ℝ) * t ^ (-s.re - 1) := by
      rw [← Real.rpow_add ht0]; ring_nf
    rw [hsplit]
    have := hb t ht1
    nlinarith
  · rw [integral_add (i1.const_mul B) (i2.const_mul η), integral_const_mul, integral_const_mul,
      integral_Ioi_rpow_of_lt e1 zero_lt_one, integral_Ioi_rpow_of_lt e2 zero_lt_one, Real.one_rpow,
      Real.one_rpow]
    have h3 : s.re - 1 / 4 ≠ 0 := by linarith
    have h4 : s.re ≠ 0 := by linarith
    rw [show -s.re - 1 + 1 = -s.re by ring, show 1 / 4 - s.re - 1 + 1 = -(s.re - 1 / 4) by ring]
    field_simp

end EvelynLinfootFC
