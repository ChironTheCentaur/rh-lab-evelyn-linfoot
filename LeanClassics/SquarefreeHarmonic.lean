import LeanClassics.TotientLogSum

/-!
# `∑_{n ≤ N} μ(n)²/n = (6/π²) log N + O(1)`

`abs_sum_moebius_sq_div_sub_le`: there is a constant `C` such that for every natural `N ≥ 1`,
`|∑_{1 ≤ n ≤ N, n squarefree} 1/n − (6/π²) log N| ≤ C`, written with `μ(n)²` as the indicator
of squarefree `n`.

Proof. `μ(n)² = ∑_{k² ∣ n} μ(k)` (`SquarefreeCount.sum_moebius_sq_dvd`) and
`∑_{n ≤ N, m ∣ n} 1/n = H(⌊N/m⌋)/m` (`sum_dvd_inv`) give
`∑_{n ≤ N} μ(n)²/n = ∑_{k ≤ N} (μ(k)/k²) H(⌊N/k²⌋)`. For `k² ≤ N`,
`|H(⌊N/k²⌋) − log(N/k²)| ≤ 1` (`TotientLogSum.harmonic_sub_log_le`); for `k² > N` the term is
`0` and `|log(N/k²)| ≤ 2 log k`. With `∑ log k/k²` convergent
(`TotientLogSum.summable_log_div_sq`) and `log N |6/π² − ∑_{k ≤ N} μ(k)/k²| ≤ 1`
(`SquarefreeCount.tail_le`), the constant is `π²/6 + 4 ∑' log k/k² + 1`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.SquarefreeHarmonic

open LeanClassics.TotientLogSum (harmonic_sub_log_le summable_log_div_sq)

/-- `∑_{n ≤ N, m ∣ n} 1/n = H(⌊N/m⌋)/m` for `m > 0`. -/
lemma sum_dvd_inv {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Ioc 0 N with m ∣ n, 1 / (n : ℝ) = 1 / (m : ℝ) * (harmonic (N / m) : ℝ) := by
  have himg : {n ∈ Ioc 0 N | m ∣ n} = (Ioc 0 (N / m)).image (fun j => m * j) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, ⟨j, rfl⟩⟩
      refine ⟨j, ⟨Nat.pos_of_mul_pos_left hn0, ?_⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hm, mul_comm]
      exact hnN
    · rintro ⟨j, ⟨hj0, hjN⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hm hj0, ?_⟩, Dvd.intro j rfl⟩
      rw [Nat.le_div_iff_mul_le hm, mul_comm] at hjN
      exact hjN
  have hinj : Set.InjOn (fun j => m * j) (Ioc 0 (N / m) : Set ℕ) :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h
  rw [himg, sum_image hinj, harmonic_eq_sum_Icc,
    show Icc 1 (N / m) = Ioc 0 (N / m) by ext; simp; omega]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [one_div, one_div, mul_inv]

/-- `∑_{n ≤ N} μ(n)²/n = ∑_{k ≤ N} (μ(k)/k²) H(⌊N/k²⌋)`. -/
lemma sum_moebius_sq_div_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ((ArithmeticFunction.moebius n : ℝ) ^ 2) / n =
      ∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (harmonic (N / (k * k)) : ℝ) := by
  have h1 : ∀ n ∈ Ioc 0 N, ((ArithmeticFunction.moebius n : ℝ) ^ 2) / n =
      ∑ k ∈ Ioc 0 N, if k * k ∣ n then (ArithmeticFunction.moebius k : ℝ) * (1 / (n : ℝ))
        else 0 := fun n hn => by
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
    have h := LeanClassics.SquarefreeCount.sum_moebius_sq_dvd hn0.ne'
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    rw [← h', sum_div, ← sum_filter]
    have hf : {k ∈ Ioc 0 N | k * k ∣ n} = {d ∈ n.divisors | d * d ∣ n} := by
      ext k
      simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hk0, -⟩, hkk⟩
        exact ⟨⟨(Dvd.intro k rfl).trans hkk, hn0.ne'⟩, hkk⟩
      · rintro ⟨⟨hkn, -⟩, hkk⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hkn hn0, (Nat.le_of_dvd hn0 hkn).trans hnN⟩, hkk⟩
    rw [hf]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := (mem_Ioc.mp hk).1
  rw [← sum_filter, ← mul_sum, sum_dvd_inv (Nat.mul_pos hk0 hk0)]
  push_cast
  ring

/-- `|H(⌊N/k²⌋) − (log N − 2 log k)| ≤ 1 + 2 log k` for `1 ≤ k ≤ N`. -/
lemma harmonic_sq_sub_le {N k : ℕ} (hN : 1 ≤ N) (hk : k ∈ Ioc 0 N) :
    |(harmonic (N / (k * k)) : ℝ) - (Real.log N - 2 * Real.log k)| ≤ 1 + 2 * Real.log k := by
  have hk0 : 0 < k := (mem_Ioc.mp hk).1
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk0)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have e : Real.log N - 2 * Real.log k = Real.log ((N : ℝ) / ((k * k : ℕ) : ℝ)) := by
    rw [Real.log_div hNr.ne' (by positivity), Nat.cast_mul, Real.log_mul hkr.ne' hkr.ne']
    ring
  by_cases hkk : k * k ≤ N
  · have h := harmonic_sub_log_le (N := N) (d := k * k)
      (mem_Ioc.mpr ⟨Nat.mul_pos hk0 hk0, hkk⟩)
    rw [e]
    linarith
  · replace hkk := not_le.mp hkk
    rw [Nat.div_eq_of_lt hkk, harmonic_zero, Rat.cast_zero, zero_sub, abs_neg]
    have hlt : Real.log N ≤ 2 * Real.log k := by
      have h1 : (N : ℝ) ≤ (k : ℝ) ^ 2 := by
        rw [sq]; exact_mod_cast hkk.le
      have h2 := Real.log_le_log hNr h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    rw [abs_le]
    constructor <;> linarith

theorem abs_sum_moebius_sq_div_sub_le : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Ioc 0 N, ((ArithmeticFunction.moebius n : ℝ) ^ 2) / n - 6 / π ^ 2 * Real.log N|
      ≤ C := by
  set L := ∑' d : ℕ, Real.log d / (d : ℝ) ^ 2
  refine ⟨π ^ 2 / 6 + 4 * L + 1, fun N hN => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogk : ∀ k ∈ Ioc 0 N, 0 ≤ Real.log k := fun k hk =>
    Real.log_nonneg (by exact_mod_cast (mem_Ioc.mp hk).1)
  have hμ : ∀ k, |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := fun k => by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hLs : ∑ k ∈ Ioc 0 N, Real.log k / (k : ℝ) ^ 2 ≤ L :=
    summable_log_div_sq.sum_le_tsum _ fun d _ => by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (by positivity)
  have hZs : ∑ k ∈ Ioc 0 N, 1 / (k : ℝ) ^ 2 ≤ π ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]
    exact hasSum_zeta_two.summable.sum_le_tsum _ fun d _ => by positivity
  rw [sum_moebius_sq_div_eq]
  set S := ∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2
  set R := ∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 * Real.log k
  have hsplit : ∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
      (Real.log N - 2 * Real.log k) = Real.log N * S - 2 * R := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have h1 : |∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
      (harmonic (N / (k * k)) : ℝ) - (Real.log N * S - 2 * R)| ≤ π ^ 2 / 6 + 2 * L := by
    rw [← hsplit, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ k ∈ Ioc 0 N, |(ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (harmonic (N / (k * k)) : ℝ) - (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
        (Real.log N - 2 * Real.log k)| ≤ 1 / (k : ℝ) ^ 2 + 2 * (Real.log k / (k : ℝ) ^ 2) :=
      fun k hk => by
      rw [← mul_sub, abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
      calc |(ArithmeticFunction.moebius k : ℝ)| / (k : ℝ) ^ 2 *
            |(harmonic (N / (k * k)) : ℝ) - (Real.log N - 2 * Real.log k)| ≤
            1 / (k : ℝ) ^ 2 * (1 + 2 * Real.log k) :=
            mul_le_mul (div_le_div_of_nonneg_right (hμ k) (by positivity))
              (harmonic_sq_sub_le hN hk) (abs_nonneg _) (by positivity)
        _ = 1 / (k : ℝ) ^ 2 + 2 * (Real.log k / (k : ℝ) ^ 2) := by ring
    refine (sum_le_sum hb).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    linarith
  have h2 : |R| ≤ L := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k hk => ?_).trans hLs)
    rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2),
      abs_of_nonneg (hlogk k hk)]
    calc |(ArithmeticFunction.moebius k : ℝ)| / (k : ℝ) ^ 2 * Real.log k ≤
          1 / (k : ℝ) ^ 2 * Real.log k :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hμ k) (by positivity))
            (hlogk k hk)
      _ = Real.log k / (k : ℝ) ^ 2 := by ring
  have h3 : |Real.log N * S - 6 / π ^ 2 * Real.log N| ≤ 1 := by
    have e : Real.log N * S - 6 / π ^ 2 * Real.log N = -(Real.log N * (6 / π ^ 2 - S)) := by
      ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg hlog]
    have hT := LeanClassics.SquarefreeCount.tail_le hN
    have hlN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hNr).trans (by linarith)
    calc Real.log N * |6 / π ^ 2 - S| ≤ Real.log N * (1 / N) :=
          mul_le_mul_of_nonneg_left hT hlog
      _ = Real.log N / N := by ring
      _ ≤ 1 := (div_le_one hNr).mpr hlN
  calc |∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (harmonic (N / (k * k)) : ℝ) - 6 / π ^ 2 * Real.log N|
      ≤ |∑ k ∈ Ioc 0 N, (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2 *
          (harmonic (N / (k * k)) : ℝ) - (Real.log N * S - 2 * R)| + |-(2 * R)| +
        |Real.log N * S - 6 / π ^ 2 * Real.log N| := by
        refine le_of_eq_of_le ?_ (abs_add_three _ _ _)
        congr 1
        ring
    _ ≤ (π ^ 2 / 6 + 2 * L) + 2 * L + 1 := by
        rw [abs_neg, abs_mul, abs_two]
        linarith
    _ = π ^ 2 / 6 + 4 * L + 1 := by ring

end LeanClassics.SquarefreeHarmonic
