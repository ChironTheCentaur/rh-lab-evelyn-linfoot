import Mathlib

/-!
# Squarefree numbers: `#{n ≤ N squarefree} = 6N/π² + O(√N)`

`abs_card_squarefree_sub_le`: for `N ≥ 1`, `|#{1 ≤ n ≤ N : n squarefree} − 6N/π²| ≤ 5 √N`.

Proof. `μ(n)² = ∑_{d² ∣ n} μ(d)` (`sum_moebius_sq_dvd`, writing `n = b² a` with `a` squarefree,
so that `d² ∣ n ↔ d ∣ b`), hence `∑_{n ≤ N} μ(n)² = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`
(`sum_moebius_sq_eq`). Then `∑_d μ(d)/d² = 1/ζ(2) = 6/π²` (`tsum_moebius_div_sq`, from Mathlib's
`LSeries_zeta_mul_Lseries_moebius` and `riemannZeta_two`), whose tail beyond `M` is at most `1/M`
(`tail_le`).
-/

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace LeanClassics.SquarefreeCount

/-- With `a` squarefree, `d² ∣ b² a ↔ d ∣ b`. -/
lemma sq_dvd_iff {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0) :
    d * d ∣ b ^ 2 * a ↔ d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  constructor
  · intro h
    rw [← Nat.factorization_le_iff_dvd hd hb]
    rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)] at h
    intro p
    have hp := h p
    have h1 := ha.natFactorization_le_one p
    rw [Nat.factorization_mul hd hd, Nat.factorization_mul (pow_ne_zero 2 hb) ha0,
      Nat.factorization_pow] at hp
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hp
    omega
  · intro h
    exact (Nat.mul_dvd_mul h h).trans (by rw [sq]; exact Dvd.intro a rfl)

/-- `∑_{d² ∣ n} μ(d) = μ(n)²` for `n ≠ 0`. -/
lemma sum_moebius_sq_dvd {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with d * d ∣ n, (μ d : ℤ) = μ n ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have hb : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have hfil : n.divisors.filter (fun d => d * d ∣ n) = b.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨-, -⟩, h⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hn h
      exact ⟨(sq_dvd_iff ha hb hd).mp (hab ▸ h), hb⟩
    · rintro ⟨h, -⟩
      have hd : d ≠ 0 := by rintro rfl; simp at h; exact hb h
      have h2 := (sq_dvd_iff ha hb hd).mpr h
      rw [hab] at h2
      exact ⟨⟨(Dvd.intro d rfl).trans h2, hn⟩, h2⟩
  rw [hfil, moebius_sq]
  have hz : ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ => f b) moebius_mul_coe_zeta
    simp only [coe_mul_zeta_apply, one_apply] at this
    exact this
  rw [hz]
  by_cases hb1 : b = 1
  · subst hb1
    simp only [one_pow, one_mul] at hab
    simp [hab ▸ ha]
  · have hns : ¬ Squarefree n := fun hs => hb1 (Nat.isUnit_iff.mp
      (hs b (by rw [← hab, sq]; exact Dvd.intro a rfl)))
    simp [hb1, hns]

/-- `∑_{n ≤ N} μ(n)² = ∑_{d ≤ √N} μ(d) ⌊N/d²⌋`. -/
lemma sum_moebius_sq_eq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (μ n : ℤ) ^ 2 =
      ∑ d ∈ Ioc 0 (Nat.sqrt N), (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := by
  have h1 : ∀ n ∈ Ioc 0 N, (μ n : ℤ) ^ 2 =
      ∑ d ∈ Ioc 0 N, if d * d ∣ n then (μ d : ℤ) else 0 := fun n hn => by
    have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
    rw [← sum_moebius_sq_dvd hn0, sum_ite, sum_const_zero, add_zero]
    congr 1
    ext d
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, -⟩, h⟩
      have hd0 : d ≠ 0 := by rintro rfl; simp at h; exact hn0 h
      exact ⟨⟨Nat.pos_of_ne_zero hd0, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn).trans
        (mem_Ioc.mp hn).2⟩, h⟩
    · rintro ⟨⟨hd0, -⟩, h⟩
      exact ⟨⟨(Dvd.intro d rfl).trans h, hn0⟩, h⟩
  rw [sum_congr rfl h1, sum_comm]
  have h2 : ∀ d ∈ Ioc 0 N, (∑ n ∈ Ioc 0 N, if d * d ∣ n then (μ d : ℤ) else 0) =
      (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := fun d _ => by
    rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  rw [sum_congr rfl h2]
  symm
  refine sum_subset (Ioc_subset_Ioc_right (Nat.sqrt_le_self N)) fun d hd hnd => ?_
  have hd' : Nat.sqrt N < d := by
    simp only [mem_Ioc, not_and, not_le] at hd hnd; exact hnd hd.1
  have : N < d * d := by
    have := Nat.lt_succ_sqrt' N
    rw [sq] at this
    exact this.trans_le (Nat.mul_le_mul hd' hd')
  rw [Nat.div_eq_of_lt this]
  simp

/-- `∑ μ(d)/d² = 6/π²`. -/
lemma tsum_moebius_div_sq : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 = 6 / π ^ 2 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hL : LSeries (fun n => (μ n : ℂ)) 2 = 6 / (π : ℂ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hπ)]
    linear_combination (6 : ℂ) * h
  have hc : ((∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) = LSeries (fun n => (μ n : ℂ)) 2 := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn]
    push_cast
    norm_cast
  have := hc.trans hL
  exact_mod_cast this

lemma summable_moebius_div_sq : Summable fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2 := by
  refine (Real.summable_one_div_nat_pow.mpr one_lt_two).of_norm_bounded fun d => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
  have : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  exact div_le_div_of_nonneg_right this (by positivity)

/-- `|∑ μ(d)/d² − ∑_{d ≤ M} μ(d)/d²| ≤ 1/M` for `M ≥ 1`. -/
lemma tail_le {M : ℕ} (hM : 1 ≤ M) :
    |6 / π ^ 2 - ∑ d ∈ Ioc 0 M, (μ d : ℝ) / (d : ℝ) ^ 2| ≤ 1 / (M : ℝ) := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2
  have e := summable_moebius_div_sq.sum_add_tsum_nat_add (M + 1)
  have hI : Ioc 0 M = Ico 1 (M + 1) := by ext; simp; omega
  have hR : ∑ d ∈ range (M + 1), f d = ∑ d ∈ Ioc 0 M, f d := by
    rw [sum_range_succ', hI, sum_Ico_eq_sum_range]
    simp [f, add_comm]
  rw [← tsum_moebius_div_sq, ← e, hR]
  simp only [add_sub_cancel_left]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : ∀ k : ℕ, |f (k + (M + 1))| ≤ 1 / ((k : ℝ) + M) - 1 / ((k : ℝ) + 1 + M) := fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + M := by positivity
    have h1 : |f (k + (M + 1))| ≤ 1 / (((k : ℝ) + 1 + M)) ^ 2 := by
      simp only [f, abs_div]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + (M + 1) : ℕ) : ℝ) ^ 2)]
      have : |(μ (k + (M + 1)) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      refine (div_le_div_of_nonneg_right this (by positivity)).trans (le_of_eq ?_)
      push_cast; ring_nf
    refine h1.trans ?_
    rw [div_sub_div _ _ hk.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsb : Summable fun k : ℕ => |f (k + (M + 1))| :=
    ((summable_nat_add_iff (M + 1)).mpr summable_moebius_div_sq).abs
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

/-- **The number of squarefree `n ≤ N` is `6N/π² + O(√N)`**: for `N ≥ 1`,
`|#{n ≤ N : n squarefree} − 6N/π²| ≤ 5 √N`. -/
theorem abs_card_squarefree_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |((((Ioc 0 N).filter Squarefree).card : ℕ) : ℝ) - 6 * N / π ^ 2| ≤ 5 * √(N : ℝ) := by
  set M := Nat.sqrt N
  have hM1 : 1 ≤ M := Nat.sqrt_pos.mpr hN
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMs : (M : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hsM : √(N : ℝ) < M + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hNs : (N : ℝ) = √(N : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg N)).symm
  -- the count as a sum over `d ≤ M`
  have hcZ : ((((Ioc 0 N).filter Squarefree).card : ℕ) : ℤ) =
      ∑ d ∈ Ioc 0 M, (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := by
    rw [← sum_moebius_sq_eq, sum_congr rfl (fun n _ => moebius_sq), sum_boole]
  have hc : ((((Ioc 0 N).filter Squarefree).card : ℕ) : ℝ) =
      ∑ d ∈ Ioc 0 M, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcZ
    push_cast at this
    exact this
  -- floor errors
  have hE : |(N : ℝ) * ∑ d ∈ Ioc 0 M, (μ d : ℝ) / (d : ℝ) ^ 2 -
      ∑ d ∈ Ioc 0 M, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)| ≤ M := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ d ∈ Ioc 0 M, |(N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2) -
        (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)| ≤ 1 := fun d hd => by
      have hd0 : 0 < d * d := Nat.mul_pos (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).1
      have hdr : (0 : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast hd0
      have e : (N : ℝ) * ((μ d : ℝ) / (d : ℝ) ^ 2) - (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) =
          (μ d : ℝ) * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ)) := by
        push_cast; ring
      rw [e, abs_mul]
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have hdm := Nat.div_add_mod N (d * d)
      have hlt : N % (d * d) < d * d := Nat.mod_lt _ hd0
      have eN : (N : ℝ) = ((d * d : ℕ) : ℝ) * ((N / (d * d) : ℕ) : ℝ) +
          ((N % (d * d) : ℕ) : ℝ) := by exact_mod_cast hdm.symm
      have hlt' : ((N % (d * d) : ℕ) : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast hlt
      have h0 : 0 ≤ (N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ) := by
        rw [sub_nonneg]; exact Nat.cast_div_le
      have h1 : (N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ) ≤ 1 := by
        rw [div_sub' hdr.ne', div_le_one hdr, eN]
        nlinarith
      rw [abs_of_nonneg h0]
      calc |(μ d : ℝ)| * ((N : ℝ) / ((d * d : ℕ) : ℝ) - ((N / (d * d) : ℕ) : ℝ))
          ≤ 1 * 1 := mul_le_mul hμ h1 h0 zero_le_one
        _ = 1 := by ring
    refine (sum_le_sum this).trans ?_
    simp
  have hT := tail_le hM1
  -- `N/M ≤ 4M`
  have hNlt : (N : ℝ) < ((M : ℝ) + 1) ^ 2 := by
    rw [hNs]; exact pow_lt_pow_left₀ hsM (by positivity) (by norm_num)
  have hNM : (N : ℝ) / M ≤ 4 * M := by
    rw [div_le_iff₀ hMpos]; nlinarith
  set S := ∑ d ∈ Ioc 0 M, (μ d : ℝ) / (d : ℝ) ^ 2
  set Q := ∑ d ∈ Ioc 0 M, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)
  have key : Q - 6 * N / π ^ 2 = -((N : ℝ) * S - Q) - N * (6 / π ^ 2 - S) := by ring
  rw [hc, key]
  have h2 : |(N : ℝ) * (6 / π ^ 2 - S)| ≤ 4 * (M : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc (N : ℝ) * |6 / π ^ 2 - S| ≤ N * (1 / M) :=
          mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg N)
      _ = N / M := by ring
      _ ≤ 4 * (M : ℝ) := hNM
  calc |-((N : ℝ) * S - Q) - N * (6 / π ^ 2 - S)|
      ≤ |(N : ℝ) * S - Q| + |(N : ℝ) * (6 / π ^ 2 - S)| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_neg]
    _ ≤ (M : ℝ) + 4 * (M : ℝ) := add_le_add hE h2
    _ ≤ 5 * √(N : ℝ) := by linarith

end LeanClassics.SquarefreeCount
