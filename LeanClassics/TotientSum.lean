import LeanClassics.SquarefreeCount

/-!
# `∑_{n ≤ N} φ(n) = 3N²/π² + O(N log N)`

`abs_sum_totient_sub_le`: for `N ≥ 1`, `|∑_{1 ≤ n ≤ N} φ(n) − 3N²/π²| ≤ N (log N + 1)`.

Proof. Möbius inversion of `∑_{d ∣ n} φ(d) = n` (Mathlib's `Nat.sum_totient` and
`sum_eq_iff_sum_mul_moebius_eq`) gives `φ = μ * id`, so
`∑_{n ≤ N} φ(n) = ∑_{a ≤ N} μ(a) K_a(K_a + 1)/2` with `K_a = ⌊N/a⌋` (Mathlib's
`sum_Ioc_mul_eq_sum_sum`). Each term is `μ(a) N²/(2a²)` up to `N/(2a)`; the sum of these
errors is at most `(N/2)(1 + log N)` (Mathlib's `harmonic_le_one_add_log`), and
`(N²/2) |6/π² − ∑_{a ≤ N} μ(a)/a²| ≤ N/2` (`SquarefreeCount.tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.TotientSum

open LeanClassics.SquarefreeCount (tail_le)

/-- `∑_{n ≤ N} φ(n) = ∑_{a ≤ N} μ(a) ∑_{b ≤ N/a} b`. -/
lemma sum_totient_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n.totient : ℤ) =
      ∑ a ∈ Ioc 0 N, (μ a : ℤ) * ∑ b ∈ Ioc 0 (N / a), (b : ℤ) := by
  set g : ArithmeticFunction ℤ := ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
    ArithmeticFunction ℤ)
  have hg : ∀ n, g n = (n : ℤ) := fun n => by simp [g]
  have hφ : ∀ n > 0, (((μ : ArithmeticFunction ℤ) * g) n) = (n.totient : ℤ) := by
    have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := fun n => (n.totient : ℤ))
      (g := fun n => (n : ℤ))).mp fun n _ => by exact_mod_cast Nat.sum_totient n
    intro n hn
    rw [mul_apply, ← h n hn]
    refine sum_congr rfl fun x _ => ?_
    rw [hg, Int.cast_id]
  rw [← sum_congr rfl fun n hn => hφ n (mem_Ioc.mp hn).1, sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [hg]

lemma gauss (K : ℕ) : ∑ b ∈ Ioc 0 K, (b : ℝ) = K * (K + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le K), ih]
    push_cast; ring

/-- `|K(K + 1)/2 − x²/2| ≤ x/2` for `K = ⌊x⌋`, `x = N/a ≥ 1`. -/
lemma term_le {N a : ℕ} (ha : a ∈ Ioc 0 N) :
    |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / a) ^ 2 / 2|
      ≤ (N : ℝ) / a / 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
  set x := (N : ℝ) / a
  set K := ((N / a : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hKx : K ≤ x := Nat.cast_div_le
  have hx1 : 1 ≤ x := by
    rw [le_div_iff₀ ha0, one_mul]; exact_mod_cast (mem_Ioc.mp ha).2
  have hxK : x < K + 1 := by
    have hdm := Nat.div_add_mod N a
    have hlt : N % a < a := Nat.mod_lt _ (mem_Ioc.mp ha).1
    have eN : (N : ℝ) = a * K + ((N % a : ℕ) : ℝ) := by
      simp only [K]; exact_mod_cast hdm.symm
    have hlt' : ((N % a : ℕ) : ℝ) < a := by exact_mod_cast hlt
    simp only [x]
    rw [div_lt_iff₀ ha0, eN]
    nlinarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul (show x - 1 ≤ K by linarith) (le_of_lt hxK) (by linarith) hK0]
  · nlinarith [mul_le_mul hKx (show K + 1 ≤ x + 1 by linarith) (by linarith) (by linarith)]

/-- **`∑_{n ≤ N} φ(n) = 3N²/π² + O(N log N)`**: for `N ≥ 1`,
`|∑_{1 ≤ n ≤ N} φ(n) − 3N²/π²| ≤ N (log N + 1)`. -/
theorem abs_sum_totient_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - 3 * (N : ℝ) ^ 2 / π ^ 2| ≤ N * (Real.log N + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hΦ : ∑ n ∈ Ioc 0 N, (n.totient : ℝ) =
      ∑ a ∈ Ioc 0 N, (μ a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (sum_totient_eq N)
    push_cast at this
    rw [this]
    refine sum_congr rfl fun a _ => ?_
    rw [gauss]
  set S := ∑ a ∈ Ioc 0 N, (μ a : ℝ) / (a : ℝ) ^ 2
  have hmain : |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - (N : ℝ) ^ 2 / 2 * S| ≤
      (N : ℝ) / 2 * (1 + Real.log N) := by
    rw [hΦ, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ a ∈ Ioc 0 N, |(μ a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) -
        (N : ℝ) ^ 2 / 2 * ((μ a : ℝ) / (a : ℝ) ^ 2)| ≤ (N : ℝ) / 2 * (1 / (a : ℝ)) :=
      fun a ha => by
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
      have e : (μ a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) -
          (N : ℝ) ^ 2 / 2 * ((μ a : ℝ) / (a : ℝ) ^ 2) = (μ a : ℝ) *
          (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 - ((N : ℝ) / a) ^ 2 / 2) := by
        field_simp
      rw [e, abs_mul]
      have hμ : |(μ a : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      calc |(μ a : ℝ)| * |((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2 -
            ((N : ℝ) / a) ^ 2 / 2| ≤ 1 * ((N : ℝ) / a / 2) :=
            mul_le_mul hμ (term_le ha) (abs_nonneg _) zero_le_one
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
  have h2 : |(N : ℝ) ^ 2 / 2 * S - 3 * (N : ℝ) ^ 2 / π ^ 2| ≤ (N : ℝ) / 2 := by
    have e : (N : ℝ) ^ 2 / 2 * S - 3 * (N : ℝ) ^ 2 / π ^ 2 =
        -((N : ℝ) ^ 2 / 2 * (6 / π ^ 2 - S)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |6 / π ^ 2 - S| ≤ (N : ℝ) ^ 2 / 2 * (1 / N) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (N : ℝ) / 2 := by field_simp
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - 3 * (N : ℝ) ^ 2 / π ^ 2|
      ≤ |∑ n ∈ Ioc 0 N, (n.totient : ℝ) - (N : ℝ) ^ 2 / 2 * S| +
        |(N : ℝ) ^ 2 / 2 * S - 3 * (N : ℝ) ^ 2 / π ^ 2| := abs_sub_le _ _ _
    _ ≤ (N : ℝ) / 2 * (1 + Real.log N) + (N : ℝ) / 2 := add_le_add hmain h2
    _ ≤ N * (Real.log N + 1) := by nlinarith

end LeanClassics.TotientSum
