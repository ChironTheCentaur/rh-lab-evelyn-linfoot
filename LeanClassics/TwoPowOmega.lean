import LeanClassics.SquarefreeHarmonic

/-!
# `∑_{n ≤ N} 2^{ω(n)} = (6/π²) N log N + O(N)`

`abs_sum_two_pow_omega_sub_le`: there is a constant `C` such that for every natural `N ≥ 1`,
`|∑_{1 ≤ n ≤ N} 2^{ω(n)} − (6/π²) N log N| ≤ C N`, where `ω(n)` is the number of distinct
prime factors (Mathlib's `ArithmeticFunction.cardDistinctFactors`).

Proof. `2^{ω(n)}` counts the squarefree divisors of `n` (Mathlib's
`sum_divisors_filter_squarefree`), so `2^{ω(n)} = ∑_{d ∣ n} μ(d)²` (`two_pow_omega_eq`) and
`∑_{n ≤ N} 2^{ω(n)} = ∑_{d ≤ N} μ(d)² ⌊N/d⌋` (`RatioSums.sum_sum_divisors`). This is
`N ∑_{d ≤ N} μ(d)²/d` up to at most `N`, and
`SquarefreeHarmonic.abs_sum_moebius_sq_div_sub_le` finishes.
-/

open Real Finset

noncomputable section

namespace LeanClassics.TwoPowOmega

/-- `2^{ω(n)} = ∑_{d ∣ n} μ(d)²` for `n ≠ 0`. -/
lemma two_pow_omega_eq {n : ℕ} (hn : n ≠ 0) :
    (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 := by
  have h1 : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 =
      ∑ d ∈ n.divisors with Squarefree d, (1 : ℝ) := by
    rw [sum_filter]
    refine sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      simp
  rw [h1, Nat.sum_divisors_filter_squarefree hn, sum_const, Finset.card_powerset,
    Nat.factors_eq, ArithmeticFunction.cardDistinctFactors_apply]
  simp only [nsmul_eq_mul, mul_one]
  push_cast
  congr 1

/-- `∑_{n ≤ N} 2^{ω(n)} = ∑_{d ≤ N} μ(d)² ⌊N/d⌋`. -/
lemma sum_two_pow_omega_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) := by
  rw [sum_congr rfl fun n hn => two_pow_omega_eq (mem_Ioc.mp hn).1.ne',
    LeanClassics.RatioSums.sum_sum_divisors]

theorem abs_sum_two_pow_omega_sub_le : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ Ioc 0 N, (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n -
        6 / π ^ 2 * N * Real.log N| ≤ C * N := by
  obtain ⟨C, hC⟩ := LeanClassics.SquarefreeHarmonic.abs_sum_moebius_sq_div_sub_le
  refine ⟨C + 1, fun N hN => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_two_pow_omega_eq]
  set T := ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 / d
  have hμ2 : ∀ d, 0 ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 ∧
      (ArithmeticFunction.moebius d : ℝ) ^ 2 ≤ 1 := fun d => by
    have h : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    refine ⟨sq_nonneg _, ?_⟩
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) h
  have hE : |∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) -
      N * T| ≤ N := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ d ∈ Ioc 0 N, |(ArithmeticFunction.moebius d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) -
        N * ((ArithmeticFunction.moebius d : ℝ) ^ 2 / d)| ≤ 1 := fun d hd => by
      have hd0 : 0 < d := (mem_Ioc.mp hd).1
      have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
      have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      have h2 : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
        have := Nat.lt_div_mul_add (a := N) hd0
        have h3 : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
        rw [div_sub_one hdr.ne', div_lt_iff₀ hdr]
        linarith
      have e : (ArithmeticFunction.moebius d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) -
          N * ((ArithmeticFunction.moebius d : ℝ) ^ 2 / d) =
          (ArithmeticFunction.moebius d : ℝ) ^ 2 * (((N / d : ℕ) : ℝ) - N / d) := by
        field_simp
      rw [e, abs_mul, abs_of_nonneg (hμ2 d).1]
      have h4 : |((N / d : ℕ) : ℝ) - N / d| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc (ArithmeticFunction.moebius d : ℝ) ^ 2 * |((N / d : ℕ) : ℝ) - N / d| ≤ 1 * 1 :=
            mul_le_mul (hμ2 d).2 h4 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    refine (sum_le_sum hb).trans (le_of_eq ?_)
    simp
  have hT : |T - 6 / π ^ 2 * Real.log N| ≤ C := hC N hN
  have h2 : |(N : ℝ) * T - 6 / π ^ 2 * N * Real.log N| ≤ C * N := by
    have e : (N : ℝ) * T - 6 / π ^ 2 * N * Real.log N = N * (T - 6 / π ^ 2 * Real.log N) := by
      ring
    rw [e, abs_mul, abs_of_pos hNr, mul_comm]
    exact mul_le_mul_of_nonneg_right hT hNr.le
  calc |∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) -
          6 / π ^ 2 * N * Real.log N|
      ≤ |∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) ^ 2 * ((N / d : ℕ) : ℝ) - N * T| +
        |(N : ℝ) * T - 6 / π ^ 2 * N * Real.log N| := abs_sub_le _ _ _
    _ ≤ N + C * N := add_le_add hE h2
    _ = (C + 1) * N := by ring

end LeanClassics.TwoPowOmega
