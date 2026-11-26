import LeanClassics.TwoPowOmega

/-!
# `∑ μ(n)²/n^s = ζ(s)/ζ(2s)` and `∑ 2^{ω(n)}/n^s = ζ(s)²/ζ(2s)` for `Re s > 1`

`LSeries_moebius_sq`: for `Re s > 1`, `∑_{n ≥ 1} μ(n)² n^{−s} = ζ(s)/ζ(2s)` (the Dirichlet series of
the squarefree indicator).

`LSeries_two_pow_omega`: for `Re s > 1`, `∑_{n ≥ 1} 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s)`, where `ω(n)` is
the number of distinct prime factors (Mathlib's `ArithmeticFunction.cardDistinctFactors`).

Proof. `μ² = ζ * Q` with `Q(k²) = μ(k)` and `Q = 0` off the squares
(`SquarefreeCount.sum_moebius_sq_dvd`), and `∑ Q(n) n^{−s} = ∑ μ(k) k^{−2s} = 1/ζ(2s)` (Mathlib's
`LSeries_zeta_mul_Lseries_moebius` at `2s`). `2^ω = ζ * μ²` (`TwoPowOmega.two_pow_omega_eq`).
Then Mathlib's `LSeries_mul'`.
-/

open Complex ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.zeta ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeLSeries

/-- `Q(n) = μ(k)` if `n = k²`, `0` otherwise. -/
def Q : ArithmeticFunction ℤ := ⟨fun d => ∑ k ∈ d.divisors with k * k = d, μ k, by simp⟩

lemma Q_apply (d : ℕ) : Q d = ∑ k ∈ d.divisors with k * k = d, μ k := rfl

lemma Q_sq {k : ℕ} (hk : k ≠ 0) : Q (k * k) = μ k := by
  rw [Q_apply]
  have h : {j ∈ (k * k).divisors | j * j = k * k} = {k} := by
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Nat.mul_self_inj.mp h
    · intro h
      rw [h]
      exact ⟨⟨Dvd.intro k rfl, Nat.mul_ne_zero hk hk⟩, rfl⟩
  rw [h, Finset.sum_singleton]

lemma Q_support {d : ℕ} (hd : Q d ≠ 0) : ∃ k, k ≠ 0 ∧ k * k = d := by
  rw [Q_apply] at hd
  obtain ⟨k, hk, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨hkd, hkk⟩ := Finset.mem_filter.mp hk
  exact ⟨k, Nat.ne_of_gt (Nat.pos_of_mem_divisors hkd), hkk⟩

lemma abs_Q_le (d : ℕ) : |Q d| ≤ 1 := by
  by_cases h : Q d = 0
  · simp [h]
  obtain ⟨k, hk, rfl⟩ := Q_support h
  rw [Q_sq hk]
  exact abs_moebius_le_one

/-- `μ(n)²` as an arithmetic function over `ℤ`. -/
def Msq : ArithmeticFunction ℤ := ⟨fun n => μ n ^ 2, by simp⟩

/-- `μ(n)² = ∑_{d ∣ n} Q(d)`. -/
lemma zeta_mul_Q : (ζ : ArithmeticFunction ℤ) * Q = Msq := by
  ext n
  rw [coe_zeta_mul_apply]
  change ∑ d ∈ n.divisors, Q d = μ n ^ 2
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [← LeanClassics.SquarefreeCount.sum_moebius_sq_dvd hn]
  simp only [Q_apply]
  rw [Finset.sum_comm' (t' := {k ∈ n.divisors | k * k ∣ n}) (s' := fun k => {k * k})]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_singleton]
  · intro d k
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdn, -⟩, ⟨hkd, hd0⟩, hkk⟩
      refine ⟨hkk.symm, ⟨hkd.trans hdn, hn⟩, ?_⟩
      rw [hkk]
      exact hdn
    · rintro ⟨hd, ⟨hkn, -⟩, hkkn⟩
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hn (Nat.eq_zero_of_zero_dvd hkn)
      rw [hd]
      exact ⟨⟨hkkn, hn⟩, ⟨Dvd.intro k rfl, Nat.mul_ne_zero hk0 hk0⟩, rfl⟩

lemma lseriesSummable_of_abs_le_one {f : ℕ → ℤ} (hf : ∀ n, |f n| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (f n : ℂ)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => ?_⟩
  rw [sub_self, Real.rpow_zero, mul_one, Complex.norm_intCast]
  exact_mod_cast hf n

lemma LSeries_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ)) s = (riemannZeta s)⁻¹ := by
  have h1 := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h1
  exact eq_inv_of_mul_eq_one_right h1

/-- `∑ Q(n) n^{−s} = 1/ζ(2s)` for `Re s > 1`. -/
lemma LSeries_Q {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Q n : ℂ)) s = (riemannZeta (2 * s))⁻¹ := by
  have h2s : 1 < (2 * s).re := by simp; linarith
  rw [← LSeries_moebius h2s, LSeries, LSeries]
  have hinj : Function.Injective fun k : ℕ => k * k := fun a b h => Nat.mul_self_inj.mp h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun k => ?_
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    rw [term_of_ne_zero (Nat.mul_ne_zero hk hk), term_of_ne_zero hk, Q_sq hk]
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    push_cast
    rw [Complex.natCast_mul_natCast_cpow, ← Complex.cpow_add _ _ hk', two_mul]
  · intro n hn
    rw [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hn
    rw [term_of_ne_zero hn0] at hn
    have hq : Q n ≠ 0 := by
      intro h; apply hn; simp [h]
    obtain ⟨k, -, rfl⟩ := Q_support hq
    exact ⟨k, rfl⟩

/-- `∑ μ(n)² n^{−s} = ζ(s)/ζ(2s)` for `Re s > 1`, with the series absolutely convergent. -/
theorem LSeries_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((μ n ^ 2 : ℤ) : ℂ)) s = riemannZeta s / riemannZeta (2 * s) ∧
      LSeriesSummable (fun n => ((μ n ^ 2 : ℤ) : ℂ)) s := by
  set Z : ArithmeticFunction ℂ := ((ζ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
  set F : ArithmeticFunction ℂ := ((Q : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
  have hZ : ⇑Z = fun n => ((ζ n : ℕ) : ℂ) := by
    funext n; simp only [Z, intCoe_apply]; rw [natCoe_apply]; push_cast; rfl
  have hF : ⇑F = fun n => (Q n : ℂ) := by funext n; simp [F]
  have h1 : (fun n => ((μ n ^ 2 : ℤ) : ℂ)) = ⇑(Z * F) := by
    funext n
    rw [show Z * F = (((ζ : ArithmeticFunction ℤ) * Q : ArithmeticFunction ℤ) :
      ArithmeticFunction ℂ) from intCoe_mul.symm, intCoe_apply, zeta_mul_Q]
    rfl
  have hsZ : LSeriesSummable ⇑Z s := by rw [hZ]; exact LSeriesSummable_zeta_iff.mpr hs
  have hsF : LSeriesSummable ⇑F s := by rw [hF]; exact lseriesSummable_of_abs_le_one abs_Q_le hs
  refine ⟨?_, ?_⟩
  · rw [h1, LSeries_mul' hsZ hsF, hZ, hF, LSeries_zeta_eq_riemannZeta hs, LSeries_Q hs,
      div_eq_mul_inv]
  · rw [h1]; exact LSeriesSummable_mul hsZ hsF

/-- `∑ 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s)` for `Re s > 1`. -/
theorem LSeries_two_pow_omega {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((2 : ℂ) ^ cardDistinctFactors n)) s =
      riemannZeta s ^ 2 / riemannZeta (2 * s) := by
  set Z : ArithmeticFunction ℂ := ((ζ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
  set M : ArithmeticFunction ℂ := ((Msq : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
  have hZ : ⇑Z = fun n => ((ζ n : ℕ) : ℂ) := by
    funext n; simp only [Z, intCoe_apply]; rw [natCoe_apply]; push_cast; rfl
  have hM : ⇑M = fun n => ((μ n ^ 2 : ℤ) : ℂ) := by funext n; simp only [M, intCoe_apply]; rfl
  obtain ⟨hLM, hsM'⟩ := LSeries_moebius_sq hs
  have hsZ : LSeriesSummable ⇑Z s := by rw [hZ]; exact LSeriesSummable_zeta_iff.mpr hs
  have hsM : LSeriesSummable ⇑M s := by rw [hM]; exact hsM'
  have h1 : LSeries (fun n => ((2 : ℂ) ^ cardDistinctFactors n)) s = LSeries ⇑(Z * M) s := by
    rw [LSeries, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_of_ne_zero hn, term_of_ne_zero hn]
    congr 1
    have h := LeanClassics.TwoPowOmega.two_pow_omega_eq hn
    rw [show Z * M = (((ζ : ArithmeticFunction ℤ) * Msq : ArithmeticFunction ℤ) :
      ArithmeticFunction ℂ) from intCoe_mul.symm, intCoe_apply, coe_zeta_mul_apply]
    have h' := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at h'
    rw [h']
    show _ = ((∑ x ∈ n.divisors, μ x ^ 2 : ℤ) : ℂ)
    push_cast
    rfl
  rw [h1, LSeries_mul' hsZ hsM, hZ, hM, LSeries_zeta_eq_riemannZeta hs, hLM]
  ring

end LeanClassics.SquarefreeLSeries
