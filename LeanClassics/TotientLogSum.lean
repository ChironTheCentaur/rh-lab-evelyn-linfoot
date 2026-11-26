import LeanClassics.RatioSums

/-!
# `∑_{n ≤ N} φ(n)/n² = (6/π²) log N + O(1)`

`abs_sum_totient_div_sq_sub_le`: there is a constant `C` such that for every natural `N ≥ 1`,
`|∑_{1 ≤ n ≤ N} φ(n)/n² − (6/π²) log N| ≤ C`.

Proof. `φ(n)/n² = ∑_{d ∣ n} (μ(d)/d²)(1/(n/d))` (`RatioSums.totient_div_eq`), so
`∑_{n ≤ N} φ(n)/n² = ∑_{d ≤ N} (μ(d)/d²) H(⌊N/d⌋)` with `H` the harmonic numbers (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). `|H(⌊N/d⌋) − log(N/d)| ≤ 1` (Mathlib's `log_le_harmonic_floor` and
`harmonic_le_one_add_log`), `∑ log d/d²` converges (Mathlib's `log_le_rpow_div` and
`summable_nat_rpow_inv`), and `log N |6/π² − ∑_{d ≤ N} μ(d)/d²| ≤ log N / N ≤ 1`
(`SquarefreeCount.tail_le`). The constant is `π²/6 + 1 + ∑' log d/d²`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.TotientLogSum

/-- `μ(d)/d²` as an arithmetic function over `ℝ`. -/
def F : ArithmeticFunction ℝ := ⟨fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2, by simp⟩

/-- `1/m` as an arithmetic function over `ℝ`. -/
def G : ArithmeticFunction ℝ := ⟨fun m => 1 / (m : ℝ), by simp⟩

lemma FG_apply {n : ℕ} (hn : 0 < n) : (F * G) n = (n.totient : ℝ) / (n : ℝ) ^ 2 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => F a * G b)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := LeanClassics.RatioSums.totient_div_eq hn
  have e : (n.totient : ℝ) / (n : ℝ) ^ 2 = (n.totient : ℝ) / n * (1 / n) := by
    field_simp
  rw [e, h, sum_mul]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  change (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 * (1 / ((n / d : ℕ) : ℝ)) = _
  rw [Nat.cast_div hdn hd0.ne']
  field_simp

/-- `∑_{n ≤ N} φ(n)/n² = ∑_{d ≤ N} (μ(d)/d²) H(⌊N/d⌋)`. -/
lemma sum_totient_div_sq_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n.totient : ℝ) / (n : ℝ) ^ 2 =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 * (harmonic (N / d) : ℝ) := by
  rw [← sum_congr rfl fun n hn => FG_apply (mem_Ioc.mp hn).1,
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun d _ => ?_
  change (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 * ∑ m ∈ Ioc 0 (N / d), 1 / (m : ℝ) = _
  congr 1
  rw [harmonic_eq_sum_Icc, show Icc 1 (N / d) = Ioc 0 (N / d) by ext; simp; omega]
  push_cast
  simp [one_div]

/-- `|H(⌊N/d⌋) − log(N/d)| ≤ 1` for `1 ≤ d ≤ N`. -/
lemma harmonic_sub_log_le {N d : ℕ} (hd : d ∈ Ioc 0 N) :
    |(harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / d)| ≤ 1 := by
  obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  have hK : 1 ≤ N / d := (Nat.one_le_div_iff hd0).mpr hdN
  have hKr : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hK
  have h1 := log_le_harmonic_floor ((N : ℝ) / d) (by positivity)
  rw [Nat.floor_div_eq_div] at h1
  have h2 := harmonic_le_one_add_log (N / d)
  have h3 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / d) :=
    Real.log_le_log hKr Nat.cast_div_le
  rw [abs_le]
  constructor <;> linarith

lemma summable_log_div_sq : Summable fun d : ℕ => Real.log d / (d : ℝ) ^ 2 := by
  refine (((summable_nat_rpow_inv (p := 3 / 2)).mpr (by norm_num)).mul_left 2).of_nonneg_of_le
    (fun d => by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (by positivity)) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hl := Real.log_le_rpow_div hdr.le (by norm_num : (0 : ℝ) < 1 / 2)
  have e : (d : ℝ) ^ 2 = (d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hdr]
    norm_num
  rw [e, div_le_iff₀ (by positivity)]
  have h32 : 0 < (d : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc Real.log d ≤ (d : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := hl
    _ = 2 * ((d : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (3 / 2 : ℝ)) := by
      field_simp

theorem abs_sum_totient_div_sq_sub_le : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / (n : ℝ) ^ 2 - 6 / π ^ 2 * Real.log N| ≤ C := by
  set L := ∑' d : ℕ, Real.log d / (d : ℝ) ^ 2
  refine ⟨π ^ 2 / 6 + 1 + L, fun N hN => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [sum_totient_div_sq_eq]
  set S := ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2
  set R := ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 * Real.log d
  have hsplit : ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
      Real.log ((N : ℝ) / d) = Real.log N * S - R := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hdr : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
    rw [Real.log_div hNr.ne' hdr.ne']
    ring
  have hμ : ∀ d, |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := fun d => by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  -- harmonic numbers versus logarithms
  have h1 : |∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
      (harmonic (N / d) : ℝ) - (Real.log N * S - R)| ≤ π ^ 2 / 6 := by
    rw [← hsplit, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Ioc 0 N, |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
        (harmonic (N / d) : ℝ) - (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
        Real.log ((N : ℝ) / d)| ≤ 1 / (d : ℝ) ^ 2 := fun d hd => by
      rw [← mul_sub, abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
      calc |(ArithmeticFunction.moebius d : ℝ)| / (d : ℝ) ^ 2 *
            |(harmonic (N / d) : ℝ) - Real.log ((N : ℝ) / d)| ≤ 1 / (d : ℝ) ^ 2 * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right (hμ d) (by positivity))
              (harmonic_sub_log_le hd) (abs_nonneg _) (by positivity)
        _ = 1 / (d : ℝ) ^ 2 := mul_one _
    refine (sum_le_sum hb).trans ?_
    rw [← hasSum_zeta_two.tsum_eq]
    exact hasSum_zeta_two.summable.sum_le_tsum _ fun d _ => by positivity
  -- the log-weighted Möbius sum
  have h2 : |R| ≤ L := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Ioc 0 N, |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
        Real.log d| ≤ Real.log d / (d : ℝ) ^ 2 := fun d hd => by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
      have hl : 0 ≤ Real.log d := Real.log_nonneg hd1
      rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2),
        abs_of_nonneg hl]
      calc |(ArithmeticFunction.moebius d : ℝ)| / (d : ℝ) ^ 2 * Real.log d ≤
            1 / (d : ℝ) ^ 2 * Real.log d :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hμ d) (by positivity)) hl
        _ = Real.log d / (d : ℝ) ^ 2 := by ring
    refine (sum_le_sum hb).trans ?_
    refine summable_log_div_sq.sum_le_tsum _ fun d _ => ?_
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (by positivity)
  -- the tail of `∑ μ(d)/d²`
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
  calc |∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
          (harmonic (N / d) : ℝ) - 6 / π ^ 2 * Real.log N|
      ≤ |∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
          (harmonic (N / d) : ℝ) - (Real.log N * S - R)| + |-R| +
        |Real.log N * S - 6 / π ^ 2 * Real.log N| := by
        refine le_of_eq_of_le ?_ (abs_add_three _ _ _)
        congr 1
        ring
    _ ≤ π ^ 2 / 6 + L + 1 := by
        rw [abs_neg]
        linarith
    _ = π ^ 2 / 6 + 1 + L := by ring

end LeanClassics.TotientLogSum
