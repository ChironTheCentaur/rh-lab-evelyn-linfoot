import LeanClassics.SigmaSum

/-!
# `∑_{n ≤ N} φ(n)/n = 6N/π² + O(log N)` and `∑_{n ≤ N} σ(n)/n = π²N/6 + O(log N)`

`abs_sum_totient_div_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} φ(n)/n − 6N/π²| ≤ log N + 2`.

`abs_sum_sigma_div_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} σ(n)/n − π²N/6| ≤ log N + 2`,
where `σ(n) = ∑_{d ∣ n} d` is Mathlib's `ArithmeticFunction.sigma 1`.

Proof. `φ(n)/n = ∑_{d ∣ n} μ(d)/d` (Möbius inversion of Mathlib's `Nat.sum_totient`) and
`σ(n)/n = ∑_{d ∣ n} 1/d` (Mathlib's `sigma_eq_sum_div`). For `|g(d)| ≤ 1/d`,
`∑_{n ≤ N} ∑_{d ∣ n} g(d) = ∑_{d ≤ N} g(d) ⌊N/d⌋` (Mathlib's `sum_Ioc_mul_eq_sum_sum`) is
`N ∑_{d ≤ N} g(d)/d` up to `∑_{d ≤ N} 1/d ≤ 1 + log N` (`floor_sum_le`). The remaining
`N |c − ∑_{d ≤ N} g(d)/d| ≤ 1` comes from `SquarefreeCount.tail_le` and `SigmaSum.tail_le`.
-/

open Real Finset

noncomputable section

namespace LeanClassics.RatioSums

/-- `∑_{n ≤ N} ∑_{d ∣ n} g(d) = ∑_{d ≤ N} g(d) ⌊N/d⌋`. -/
lemma sum_sum_divisors (g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d = ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
  let F : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else g d, if_pos rfl⟩
  have hF : ∀ d, d ≠ 0 → F d = g d := fun d hd => if_neg hd
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum F (ArithmeticFunction.zeta : _) N
  have hl : ∀ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d =
      (F * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := fun n _ => by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    exact sum_congr rfl fun d hd => (hF d (Nat.pos_of_mem_divisors hd).ne').symm
  rw [sum_congr rfl hl, h]
  refine sum_congr rfl fun d hd => ?_
  rw [hF d (mem_Ioc.mp hd).1.ne']
  congr 1
  rw [sum_congr rfl fun m hm => by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne
      (mem_Ioc.mp hm).1.ne']]
  simp

/-- `φ(n)/n = ∑_{d ∣ n} μ(d)/d`. -/
lemma totient_div_eq {n : ℕ} (hn : 0 < n) :
    (n.totient : ℝ) / n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) / d := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun n => (n.totient : ℤ)) (g := fun n => (n : ℤ))).mp
    (fun n _ => by exact_mod_cast Nat.sum_totient n) n hn
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))] at h
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h'
  rw [← h', sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_div hdn hd0.ne']
  field_simp

/-- `σ(n)/n = ∑_{d ∣ n} 1/d`. -/
lemma sigma_div_eq {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n = ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  rw [ArithmeticFunction.sigma_eq_sum_div]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pow_one, Nat.cast_div hdn hd0.ne']
  field_simp

/-- For `|g(d)| ≤ 1/d`: `|∑_{d ≤ N} g(d) ⌊N/d⌋ − N ∑_{d ≤ N} g(d)/d| ≤ 1 + log N`. -/
lemma floor_sum_le (g : ℕ → ℝ) (hg : ∀ d, |g d| ≤ 1 / (d : ℝ)) (N : ℕ) :
    |∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) - N * ∑ d ∈ Ioc 0 N, g d / d| ≤
      1 + Real.log N := by
  rw [mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ d ∈ Ioc 0 N, |g d * ((N / d : ℕ) : ℝ) - N * (g d / d)| ≤ 1 / (d : ℝ) :=
    fun d hd => by
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have e : g d * ((N / d : ℕ) : ℝ) - N * (g d / d) = g d * (((N / d : ℕ) : ℝ) - N / d) := by
      field_simp
    have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have h2 : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := N) hd0
      have h3 : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      rw [div_sub_one hdr.ne', div_lt_iff₀ hdr]
      linarith
    rw [e, abs_mul]
    have h4 : |((N / d : ℕ) : ℝ) - N / d| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |g d| * |((N / d : ℕ) : ℝ) - N / d| ≤ 1 / (d : ℝ) * 1 :=
          mul_le_mul (hg d) h4 (abs_nonneg _) (by positivity)
      _ = 1 / (d : ℝ) := mul_one _
  refine (sum_le_sum hb).trans ?_
  have hH : ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, show Icc 1 N = Ioc 0 N by ext; simp; omega]
    push_cast
    simp [one_div]
  rw [hH]
  exact harmonic_le_one_add_log N

theorem abs_sum_totient_div_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n - 6 * (N : ℝ) / π ^ 2| ≤ Real.log N + 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / d
  have hg : ∀ d, |g d| ≤ 1 / (d : ℝ) := fun d => by
    simp only [g, abs_div, Nat.abs_cast]
    have : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact div_le_div_of_nonneg_right this (by positivity)
  have hs : ∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n = ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_sum_divisors]
    exact sum_congr rfl fun n hn => totient_div_eq (mem_Ioc.mp hn).1
  have hS : ∑ d ∈ Ioc 0 N, g d / d =
      ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 := by
    refine sum_congr rfl fun d _ => ?_
    simp only [g]
    ring
  have h1 := floor_sum_le g hg N
  rw [← hs, hS] at h1
  have hT := LeanClassics.SquarefreeCount.tail_le hN
  set S := ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2
  have h2 : |N * S - 6 * (N : ℝ) / π ^ 2| ≤ 1 := by
    have e : N * S - 6 * (N : ℝ) / π ^ 2 = -(N * (6 / π ^ 2 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_pos hNr]
    calc (N : ℝ) * |6 / π ^ 2 - S| ≤ N * (1 / N) := mul_le_mul_of_nonneg_left hT hNr.le
      _ = 1 := by field_simp
  calc |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n - 6 * (N : ℝ) / π ^ 2|
      ≤ |∑ n ∈ Ioc 0 N, (n.totient : ℝ) / n - N * S| + |N * S - 6 * (N : ℝ) / π ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ (1 + Real.log N) + 1 := add_le_add h1 h2
    _ = Real.log N + 2 := by ring

theorem abs_sum_sigma_div_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n - π ^ 2 * (N : ℝ) / 6| ≤
      Real.log N + 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set g : ℕ → ℝ := fun d => 1 / (d : ℝ)
  have hg : ∀ d, |g d| ≤ 1 / (d : ℝ) := fun d => by
    simp only [g]
    rw [abs_of_nonneg (by positivity)]
  have hs : ∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n =
      ∑ d ∈ Ioc 0 N, g d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_sum_divisors]
    exact sum_congr rfl fun n hn => sigma_div_eq (mem_Ioc.mp hn).1
  have hS : ∑ d ∈ Ioc 0 N, g d / d = ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2 := by
    refine sum_congr rfl fun d _ => ?_
    simp only [g]
    ring
  have h1 := floor_sum_le g hg N
  rw [← hs, hS] at h1
  have hT := LeanClassics.SigmaSum.tail_le hN
  set S := ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2
  have h2 : |N * S - π ^ 2 * (N : ℝ) / 6| ≤ 1 := by
    have e : N * S - π ^ 2 * (N : ℝ) / 6 = -(N * (π ^ 2 / 6 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_pos hNr]
    calc (N : ℝ) * |π ^ 2 / 6 - S| ≤ N * (1 / N) := mul_le_mul_of_nonneg_left hT hNr.le
      _ = 1 := by field_simp
  calc |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n - π ^ 2 * (N : ℝ) / 6|
      ≤ |∑ n ∈ Ioc 0 N, (ArithmeticFunction.sigma 1 n : ℝ) / n - N * S| +
        |N * S - π ^ 2 * (N : ℝ) / 6| := abs_sub_le _ _ _
    _ ≤ (1 + Real.log N) + 1 := add_le_add h1 h2
    _ = Real.log N + 2 := by ring

end LeanClassics.RatioSums
