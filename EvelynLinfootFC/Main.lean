import EvelynLinfootFC.Mellin
import LeanClassics.Hardy
import LeanClassics.RealZeros

/-!
# Evelyn–Linfoot: `E(x) = Q(x) − 6x/π²` is not `o(x^{1/4})`

Assume `E = o(n^{1/4})`. By `EvelynLinfootFC.Mellin`, `G(s) = ∫_1^∞ E(⌊t⌋) t^{−s−1} dt` is holomorphic on
`Re s > 1/4` and `s G(s) = ζ(s)/ζ(2s) − (6/π²) ζ(s)` on `Re s > 1`. On the convex region
`U = {Re s > 1/4, Im s > 0}` (which avoids the poles `s = 1` of `ζ(s)` and `s = 1/2` of `ζ(2s)`) the identity theorem
gives

  `ζ(s) (1 − (6/π²) ζ(2s)) = ζ(2s) · s G(s)`                                          (`identity`)

Take a zero `ρ` of ζ on the critical line with `Im ρ > 0` (Hardy's theorem, `LeanClassics.Hardy`; `Im ρ ≠ 0` because
`ζ(1/2) ≠ 0`, `LeanClassics.RealZeros`).

* `ζ(ρ/2) ≠ 0` (`caseB`): at `s = ρ/2 + ε` the left side tends to `ζ(ρ/2) ≠ 0` as `ε → 0+`, while the right side is
  at most `‖ζ(ρ + 2ε)‖ ‖s‖ (4B + η/ε) ≤ 2Cε · M · (4B + η/ε)` (ζ is Lipschitz at its zero ρ; `η` is free in the
  `o`-hypothesis and `B` depends on it, `Mellin.norm_G_le`), which is below `‖ζ(ρ/2)‖/2` for `η` small and then `ε`
  small.
* `ζ(ρ/2) = 0` (`caseA`): the functional equation gives a zero `w₀ = conj(1 − ρ/2)` with `Re w₀ = 3/4`, `Im w₀ > 0`.
  For a zero `w` with `1/2 < Re w < 1`, `Im w > 0`, the identity at `s = w/2 ∈ U` gives `ζ(w/2) = 0`, hence
  (functional equation, conjugation) a zero `T w = conj(1 − w/2)` of the same kind, with `‖T w − 2/3‖ = ‖w − 2/3‖/2`.
  So zeros of ζ accumulate at `2/3` from `Im > 0`, and ζ, analytic on the connected set `ℂ \ {1}`, would vanish
  identically; but `ζ(2) = π²/6`.

No RH, no zero certificate: the only arithmetic input about zeros is Hardy's theorem.
-/

open Complex Filter Asymptotics Topology Set
open scoped ComplexConjugate

noncomputable section

namespace EvelynLinfootFC

open Erdos969

/-- The region `Re s > 1/4`, `Im s > 0`. -/
def U : Set ℂ := {s | 1 / 4 < s.re} ∩ {s | 0 < s.im}

lemma isOpen_U : IsOpen U :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)

lemma isPreconnected_U : IsPreconnected U :=
  ((convex_halfSpace_re_gt (1 / 4)).inter (convex_halfSpace_im_gt 0)).isPreconnected

lemma ne_one_of_mem_U {s : ℂ} (hs : s ∈ U) : s ≠ 1 := fun h => by
  have := hs.2
  rw [mem_setOf_eq, h, one_im] at this
  exact lt_irrefl _ this

lemma two_mul_ne_one_of_mem_U {s : ℂ} (hs : s ∈ U) : 2 * s ≠ 1 := fun h => by
  have h2 := congrArg Complex.im h
  have := hs.2
  rw [mem_setOf_eq] at this
  simp at h2
  linarith

lemma differentiableAt_zeta_two_mul {s : ℂ} (hs : 2 * s ≠ 1) :
    DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s)) s :=
  (differentiableAt_riemannZeta hs).comp s ((differentiableAt_const 2).mul differentiableAt_id)

/-- **The identity** `ζ(s) (1 − (6/π²) ζ(2s)) = ζ(2s) · s G(s)` on `U`, under `E = o(n^{1/4})`. -/
theorem identity
    (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)))
    {s : ℂ} (hs : s ∈ U) :
    riemannZeta s * (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (2 * s)) =
      riemannZeta (2 * s) * (s * G s) := by
  have hd1 : DifferentiableOn ℂ
      (fun s => riemannZeta s * (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (2 * s))) U := by
    intro z hz
    exact ((differentiableAt_riemannZeta (ne_one_of_mem_U hz)).mul ((differentiableAt_const _).sub
      ((differentiableAt_const _).mul (differentiableAt_zeta_two_mul (two_mul_ne_one_of_mem_U hz))))).differentiableWithinAt
  have hd2 : DifferentiableOn ℂ (fun s => riemannZeta (2 * s) * (s * G s)) U := by
    intro z hz
    exact ((differentiableAt_zeta_two_mul (two_mul_ne_one_of_mem_U hz)).mul
      (differentiableAt_id.mul (differentiableAt_G h hz.1))).differentiableWithinAt
  have z0 : (2 + I : ℂ) ∈ U := by refine ⟨?_, ?_⟩ <;> norm_num
  have hev : (fun s => riemannZeta s * (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (2 * s))) =ᶠ[𝓝 (2 + I)]
      (fun s => riemannZeta (2 * s) * (s * G s)) := by
    have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 + I) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with z hz
    have hz' : 1 < z.re := hz
    have hz2 : riemannZeta (2 * z) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [show (2 * z).re = 2 * z.re by simp]; linarith)
    rw [mul_G_eq hz', mul_sub (riemannZeta (2 * z)), mul_div_cancel₀ _ hz2]
    ring
  exact (hd1.analyticOnNhd isOpen_U).eqOn_of_preconnected_of_eventuallyEq (hd2.analyticOnNhd isOpen_U)
    isPreconnected_U z0 hev hs

/-! ### Case `ζ(ρ/2) = 0`: zeros accumulate at `2/3` -/

/-- `T w = conj(1 − w/2)`. -/
def T (w : ℂ) : ℂ := conj (1 - w / 2)

lemma T_re (w : ℂ) : (T w).re = 1 - w.re / 2 := by
  simp only [T, conj_re, sub_re, one_re, div_ofNat_re]

lemma T_im (w : ℂ) : (T w).im = w.im / 2 := by
  simp only [T, conj_im, sub_im, one_im, div_ofNat_im]
  ring

lemma norm_T_sub (w : ℂ) : ‖T w - 2 / 3‖ = ‖w - 2 / 3‖ / 2 := by
  have e : T w - 2 / 3 = conj (-(w - 2 / 3) / 2) := by
    simp only [T, map_sub, map_div₀, map_neg, map_one, map_ofNat]
    ring
  rw [e, Complex.norm_conj, norm_div, norm_neg]
  simp

/-- The functional equation turns a zero `z` with `0 < Re z` (and `z ≠ 1`) into the zero `conj(1 − z)`. -/
lemma zeta_conj_one_sub_eq_zero {z : ℂ} (hz : riemannZeta z = 0) (h0 : 0 < z.re) (h1 : z ≠ 1) :
    riemannZeta (conj (1 - z)) = 0 := by
  have hn : ∀ n : ℕ, z ≠ -n := fun n hn => by
    have := congrArg Complex.re hn
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [riemannZeta_conj, riemannZeta_one_sub hn h1, hz, mul_zero, map_zero]

lemma step
    (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)))
    {w : ℂ} (hw : riemannZeta w = 0) (h1 : 1 / 2 < w.re) (h3 : 0 < w.im) :
    riemannZeta (T w) = 0 := by
  have hU : w / 2 ∈ U := ⟨by simp; linarith, by simp; linarith⟩
  have hid := identity h hU
  rw [show 2 * (w / 2) = w by ring, hw] at hid
  simp only [mul_zero, sub_zero, mul_one, zero_mul] at hid
  exact zeta_conj_one_sub_eq_zero hid (by simp; linarith) (ne_one_of_mem_U hU)

theorem caseA
    (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)))
    {w : ℂ} (hw : riemannZeta w = 0) (h1 : 1 / 2 < w.re) (h2 : w.re < 1) (h3 : 0 < w.im) : False := by
  set z : ℕ → ℂ := fun n => T^[n] w with hzdef
  have hsucc : ∀ n, z (n + 1) = T (z n) := fun n => Function.iterate_succ_apply' T n w
  have hP : ∀ n, riemannZeta (z n) = 0 ∧ 1 / 2 < (z n).re ∧ (z n).re < 1 ∧ 0 < (z n).im := by
    intro n
    induction n with
    | zero => exact ⟨hw, h1, h2, h3⟩
    | succ n ih =>
      obtain ⟨a1, a2, a3, a4⟩ := ih
      rw [hsucc, T_re, T_im]
      exact ⟨step h a1 a2 a4, by linarith, by linarith, by linarith⟩
  have hnorm : ∀ n, ‖z n - 2 / 3‖ = ‖w - 2 / 3‖ * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp [hzdef]
    | succ n ih => rw [hsucc, norm_T_sub, ih, pow_succ]; ring
  have htend : Tendsto z atTop (𝓝 (2 / 3)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp_rw [hnorm]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul ‖w - 2 / 3‖
  have htend' : Tendsto z atTop (𝓝[≠] (2 / 3)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall fun n => ?_⟩
    intro e
    have := (hP n).2.2.2
    rw [mem_singleton_iff.mp e] at this
    simp at this
  have hfreq : ∃ᶠ y in 𝓝[≠] (2 / 3 : ℂ), riemannZeta y = 0 :=
    htend'.frequently (Frequently.of_forall fun n => (hP n).1)
  have han : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_compl_singleton
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by rw [mem_compl_singleton_iff]; norm_num) hfreq
  have h2' := hzero (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by rw [mem_compl_singleton_iff]; norm_num)
  rw [riemannZeta_two, Pi.zero_apply] at h2'
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp [hπ] at h2'

/-! ### Case `ζ(ρ/2) ≠ 0`: the blow-up at `ρ/2` -/

theorem caseB
    (h : (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : ρ.re = 1 / 2) (him : 0 < ρ.im)
    (hne : riemannZeta (ρ / 2) ≠ 0) : False := by
  set A := ‖riemannZeta (ρ / 2)‖ with hA
  have hA0 : 0 < A := norm_pos_iff.mpr hne
  have hρ1 : ρ ≠ 1 := fun e => by rw [e, one_re] at hre; norm_num at hre
  have hρ21 : ρ / 2 ≠ 1 := fun e => by
    have := congrArg Complex.re e
    simp [hre] at this
    norm_num at this
  obtain ⟨C, hC0, hC⟩ := ((differentiableAt_riemannZeta hρ1).hasDerivAt.isBigO_sub).exists_pos
  set M := ‖ρ‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set η := A / (8 * C * M) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨B, hB0, hb⟩ := exists_bound h hη0
  set δ := min 1 (A / (64 * B * C * M + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  -- ζ is Lipschitz at its zero ρ, along ε ↦ ρ + 2ε
  have hpath : Tendsto (fun ε : ℝ => ρ + 2 * (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    have hc : Continuous (fun ε : ℝ => ρ + 2 * (ε : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have ev1 := hpath.eventually hC.bound
  -- the left side tends to ζ(ρ/2)
  have hc1 : ContinuousAt (fun ε : ℝ => riemannZeta (ρ / 2 + ε)) 0 :=
    (differentiableAt_riemannZeta hρ21).continuousAt.comp_of_eq (by fun_prop) (by simp)
  have hc2 : ContinuousAt (fun ε : ℝ => riemannZeta (ρ + 2 * ε)) 0 :=
    (differentiableAt_riemannZeta hρ1).continuousAt.comp_of_eq (by fun_prop) (by simp)
  have hc : ContinuousAt (fun ε : ℝ => riemannZeta (ρ / 2 + ε) *
      (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (ρ + 2 * ε))) 0 :=
    hc1.mul (continuousAt_const.sub (continuousAt_const.mul hc2))
  have hval : ‖riemannZeta (ρ / 2 + ((0 : ℝ) : ℂ)) *
      (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (ρ + 2 * ((0 : ℝ) : ℂ)))‖ = A := by
    simp [hρ, hA]
  have ev2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, A / 2 < ‖riemannZeta (ρ / 2 + ε) *
      (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (ρ + 2 * ε))‖ := by
    have ht : Tendsto (fun ε : ℝ => ‖riemannZeta (ρ / 2 + ε) *
        (1 - ((6 / Real.pi ^ 2 : ℝ) : ℂ) * riemannZeta (ρ + 2 * ε))‖) (𝓝 0) (𝓝 A) := by
      have := hc.tendsto.norm
      rwa [hval] at this
    exact (ht.eventually (lt_mem_nhds (half_lt_self hA0))).filter_mono nhdsWithin_le_nhds
  have ev3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ0
  obtain ⟨ε, hε1, hε2, ⟨hε0, hεδ⟩⟩ := (ev1.and (ev2.and ev3)).exists
  have hε1' : ε < 1 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεA : ε < A / (64 * B * C * M + 1) := lt_of_lt_of_le hεδ (min_le_right _ _)
  set s : ℂ := ρ / 2 + ε with hs
  have hsre : s.re = 1 / 4 + ε := by simp [hs, hre]; norm_num
  have hU : s ∈ U := ⟨by rw [mem_setOf_eq, hsre]; linarith, by simp [hs]; linarith⟩
  have hid := identity h hU
  rw [show 2 * s = ρ + 2 * (ε : ℂ) by rw [hs]; ring] at hid
  -- bounds on the right side
  have hX : ‖riemannZeta (ρ + 2 * (ε : ℂ))‖ ≤ C * (2 * ε) := by
    have := hε1
    simp only [hρ, sub_zero, add_sub_cancel_left] at this
    rwa [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0] at this
  have hY : ‖s‖ ≤ M := by
    have h1 : ‖ρ / 2‖ ≤ ‖ρ‖ := by rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg ρ]
    have h2 : ‖((ε : ℝ) : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    calc ‖s‖ ≤ ‖ρ / 2‖ + ‖((ε : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ M := by rw [h2, hM]; linarith
  have hZ : ‖G s‖ ≤ 4 * B + η / ε := by
    have := norm_G_le hb (s := s) (by rw [hsre]; linarith)
    rw [hsre, show 1 / 4 + ε - 1 / 4 = ε by ring] at this
    have h4 : B / (1 / 4 + ε) ≤ 4 * B := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hR : ‖riemannZeta (ρ + 2 * (ε : ℂ)) * (s * G s)‖ ≤ 8 * B * C * M * ε + A / 4 := by
    rw [norm_mul, norm_mul]
    have hYZ : ‖s‖ * ‖G s‖ ≤ M * (4 * B + η / ε) :=
      mul_le_mul hY hZ (norm_nonneg _) hM0.le
    calc ‖riemannZeta (ρ + 2 * (ε : ℂ))‖ * (‖s‖ * ‖G s‖)
        ≤ C * (2 * ε) * (M * (4 * B + η / ε)) :=
          mul_le_mul hX hYZ (by positivity) (by positivity)
      _ = 8 * B * C * M * ε + A / 4 := by
          rw [hη]; field_simp; ring
  have hsmall : 8 * B * C * M * ε < A / 8 := by
    have hpos : 0 < 64 * B * C * M + 1 := by positivity
    rw [lt_div_iff₀ hpos] at hεA
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hB0 hC0.le) hM0.le) hε0.le]
  rw [hid] at hε2
  linarith

/-- **Evelyn–Linfoot (1931).** `E(x) = Q(x) − (6/π²) x` is not `o(x^{1/4})`. -/
theorem not_isLittleO :
    ¬ (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ)) := by
  intro h
  obtain ⟨ρ0, hz0, hre0⟩ := LeanClassics.riemannZeta_zeros_on_critical_line_infinite.nonempty
  have him0 : ρ0.im ≠ 0 := by
    intro hi
    have e : ρ0 = ((1 / 2 : ℝ) : ℂ) := Complex.ext (by simp [hre0]) (by simp [hi])
    rw [e] at hz0
    exact LeanClassics.RealZeros.riemannZeta_ne_zero_of_mem_Ioo (σ := 1 / 2) (by norm_num) (by norm_num) hz0
  obtain ⟨ρ, hρ, hre, him⟩ : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im := by
    rcases lt_or_gt_of_ne him0 with hneg | hpos
    · refine ⟨conj ρ0, ?_, by simp [hre0], by simp; linarith⟩
      rw [riemannZeta_conj, hz0, map_zero]
    · exact ⟨ρ0, hz0, hre0, hpos⟩
  by_cases hz : riemannZeta (ρ / 2) = 0
  · have hρ21 : ρ / 2 ≠ 1 := fun e => by
      have := congrArg Complex.re e
      simp [hre] at this
      norm_num at this
    have hT : riemannZeta (T ρ) = 0 :=
      zeta_conj_one_sub_eq_zero hz (by simp [hre]) hρ21
    exact caseA h hT (by rw [T_re, hre]; norm_num) (by rw [T_re, hre]; norm_num) (by rw [T_im]; linarith)
  · exact caseB h hρ hre him hz

end EvelynLinfootFC
