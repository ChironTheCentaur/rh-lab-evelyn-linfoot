import LeanClassics.TotientSum

/-!
# `∑_{n ≤ N} σ(n) = π²N²/12 + O(N log N)`

`abs_sum_sigma_one_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} σ(n) − π²N²/12| ≤ N (log N + 1)`,
where `σ(n) = ∑_{d ∣ n} d` is Mathlib's `ArithmeticFunction.sigma 1`.

Proof. `σ = ζ * id` (Mathlib's `zeta_mul_pow_eq_sigma`), so
`∑_{n ≤ N} σ(n) = ∑_{a ≤ N} K_a(K_a + 1)/2` with `K_a = ⌊N/a⌋` (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). Each term is `N²/(2a²)` up to `N/(2a)` (`TotientSum.term_le`);
the sum of these errors is at most `(N/2)(1 + log N)` (Mathlib's `harmonic_le_one_add_log`),
and `(N²/2) |π²/6 − ∑_{a ≤ N} 1/a²| ≤ N/2` (`tail_le`, from Mathlib's `hasSum_zeta_two`).
-/

open Real Finset

noncomputable section

namespace LeanClassics.SigmaSum

open LeanClassics.TotientSum (gauss term_le)

/-- `∑_{n ≤ N} σ(n) = ∑_{a ≤ N} ∑_{b ≤ N/a} b`. -/
lemma sum_sigma_one_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ArithmeticFunction.sigma 1 n =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), b := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [ArithmeticFunction.zeta_apply_ne (mem_Ioc.mp ha).1.ne', one_mul]
  simp

/-- `|π²/6 − ∑_{d ≤ M} 1/d²| ≤ 1/M` for `M ≥ 1`. -/
lemma tail_le {M : ℕ} (hM : 1 ≤ M) :
    |π ^ 2 / 6 - ∑ d ∈ Ioc 0 M, 1 / (d : ℝ) ^ 2| ≤ 1 / (M : ℝ) := by
  set f : ℕ → ℝ := fun d => 1 / (d : ℝ) ^ 2
  have hs : Summable f := hasSum_zeta_two.summable
  have e := hs.sum_add_tsum_nat_add (M + 1)
  have hI : Ioc 0 M = Ico 1 (M + 1) := by ext; simp; omega
  have hR : ∑ d ∈ range (M + 1), f d = ∑ d ∈ Ioc 0 M, f d := by
    rw [sum_range_succ', hI, sum_Ico_eq_sum_range]
    simp [f, add_comm]
  rw [← hasSum_zeta_two.tsum_eq, ← e, hR]
  simp only [add_sub_cancel_left]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : ∀ k : ℕ, |f (k + (M + 1))| ≤ 1 / ((k : ℝ) + M) - 1 / ((k : ℝ) + 1 + M) := fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + M := by positivity
    have h1 : |f (k + (M + 1))| ≤ 1 / (((k : ℝ) + 1 + M)) ^ 2 := by
      simp only [f]
      rw [abs_of_nonneg (by positivity)]
      push_cast; ring_nf; rfl
    refine h1.trans ?_
    rw [div_sub_div _ _ hk.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsb : Summable fun k : ℕ => |f (k + (M + 1))| :=
    ((summable_nat_add_iff (M + 1)).mpr hs).abs
  have hn := norm_tsum_le_tsum_norm (f := fun k => f (k + (M + 1)))
    (by simpa only [Real.norm_eq_abs] using hsb)
  simp only [Real.norm_eq_abs] at hn
  refine hn.trans ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) fun n => ?_
  refine (sum_le_sum fun k _ => hb k).trans ?_
  have := sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + M)) n
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]
  simp only [Nat.cast_zero, zero_add, sub_le_self_iff]
  positivity

theorem abs_sum_sigma_one_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - π ^ 2 * (N : ℝ) ^ 2 / 12| ≤
      N * (Real.log N + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsig : ∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) =
      ∑ a ∈ Ioc 0 N, (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) := by
    have := congrArg (fun z : ℕ => (z : ℝ)) (sum_sigma_one_eq N)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun a _ => ?_
    rw [gauss]
  set S := ∑ a ∈ Ioc 0 N, 1 / (a : ℝ) ^ 2
  have hmain : |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - (N : ℝ) ^ 2 / 2 * S| ≤
      (N : ℝ) / 2 * (1 + Real.log N) := by
    rw [hsig, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ a ∈ Ioc 0 N, |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 -
        (N : ℝ) ^ 2 / 2 * (1 / (a : ℝ) ^ 2)| ≤ (N : ℝ) / 2 * (1 / (a : ℝ)) :=
      fun a ha => by
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
      have e : (N : ℝ) ^ 2 / 2 * (1 / (a : ℝ) ^ 2) = ((N : ℝ) / a) ^ 2 / 2 := by
        field_simp
      rw [e]
      calc |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / a) ^ 2 / 2|
          ≤ (N : ℝ) / a / 2 := term_le ha
        _ = (N : ℝ) / 2 * (1 / (a : ℝ)) := by ring
    refine (sum_le_sum hb).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hH : ∑ a ∈ Ioc 0 N, 1 / (a : ℝ) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, show Icc 1 N = Ioc 0 N by ext; simp; omega]
      push_cast
      simp [one_div]
    rw [hH]
    exact harmonic_le_one_add_log N
  have hT := tail_le hN
  have h2 : |(N : ℝ) ^ 2 / 2 * S - π ^ 2 * (N : ℝ) ^ 2 / 12| ≤ (N : ℝ) / 2 := by
    have e : (N : ℝ) ^ 2 / 2 * S - π ^ 2 * (N : ℝ) ^ 2 / 12 =
        -((N : ℝ) ^ 2 / 2 * (π ^ 2 / 6 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |π ^ 2 / 6 - S| ≤ (N : ℝ) ^ 2 / 2 * (1 / N) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (N : ℝ) / 2 := by field_simp
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - π ^ 2 * (N : ℝ) ^ 2 / 12|
      ≤ |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) - (N : ℝ) ^ 2 / 2 * S| +
        |(N : ℝ) ^ 2 / 2 * S - π ^ 2 * (N : ℝ) ^ 2 / 12| := abs_sub_le _ _ _
    _ ≤ (N : ℝ) / 2 * (1 + Real.log N) + (N : ℝ) / 2 := add_le_add hmain h2
    _ ≤ N * (Real.log N + 1) := by nlinarith

end LeanClassics.SigmaSum
