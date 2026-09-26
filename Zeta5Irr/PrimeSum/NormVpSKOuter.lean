/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.VpSK
public import Zeta5Irr.PrimeSum.NormFloorDoubleCount
public import Mathlib.Data.Int.Star

/-!
# The `p`-adic valuation of `S_K` at large primes

For a prime `p` with `K/3 < p ≤ 2h`, the valuation `v_p(S_K)` is, up to a bounded error,
a simple piecewise-linear function of `y = p / K`:
`|-v_p(S_K) - K (-2λ ⌊K/p⌋ + ∑_{j=1}^{5} (2λ - j p / K)₊)| ≤ 20`.

Indeed `p² > K > 2i` for all `1 ≤ i ≤ h - 1`, and `p > N`, so Legendre's formula reduces
`v_p(S_K)` to `2h ⌊K/p⌋ - 2 ∑_{i=1}^{h-1} ⌊2i/p⌋`; and `p` is odd, so `v_p(4) = 0`. By double
counting, `∑_{i=1}^{h-1} ⌊2i/p⌋ = ∑_{j ≥ 1} (h - ⌈jp/2⌉)₊`, and only `j ≤ 5` contribute since
`6p > 2K > 2h`. Each of the five terms differs from `(h - jp/2)₊ = (K/2) (2λ - jp/K)₊` by at
most `1/2`.

## Main results

* `Zeta5Irr.finsum_mem_Ici_one_div_pow_eq_div`: if `m < p²` then
  `∑_{a ≥ 1} ⌊m/p^a⌋ = ⌊m/p⌋`.
* `Zeta5Irr.padicValRat_scalingFactor_of_sq_gt`: for an odd prime `p` with `2K < p²`,
  `v_p(S_K) = 2h ⌊K/p⌋ - 12h ⌊N/p⌋ - 2 ∑_{i=1}^{h-1} ⌊2i/p⌋`.
* `Zeta5Irr.padicValRat_scalingFactor_of_lt`: the exact formula
  `v_p(S_K) = 2h ⌊K/p⌋ - 2 ∑_{j=1}^{5} (h - ⌈jp/2⌉)₊` for `K/3 < p ≤ 2h`.
* `Zeta5Irr.abs_two_mul_sub_ceil_sub_mul_posPart_le`: the one-term comparison
  `|2 (h - ⌈m/2⌉)₊ - K (2λ - m/K)₊| ≤ 1` when `h = λ K`.
* `Zeta5Irr.abs_neg_padicValRat_scalingFactor_sub_le`: the outer estimate.

## Implementation notes

* The source assumes an integer `M ≥ 40` with `K ≥ 200 M²`; this is only used to make `K`
  large, and the argument needs no more than `K > 0`, which follows from `p ≤ 2h`. The
  hypothesis is therefore dropped: the estimate holds for every `n` and every prime `p` with
  `K/3 < p ≤ 2h`.
* The proof in fact gives the bound `5`; the statement keeps the source's constant `20`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.4: the outer asymptotics.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- If `m < p²` then only the first term of Legendre's sum survives:
`∑_{a ≥ 1} ⌊m / p^a⌋ = ⌊m / p⌋`. -/
theorem finsum_mem_Ici_one_div_pow_eq_div {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m < p ^ 2) :
    ∑ᶠ a ∈ Set.Ici 1, m / p ^ a = m / p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  rw [← padicValNat_factorial_eq_finsum,
    padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow hm0.ne' hm)]
  simp

/-- For an odd prime `p` with `2K < p²`, Legendre's formula for `v_p(S_K)` reduces to its first
term: `v_p(S_K) = 2h ⌊K/p⌋ - 12h ⌊N/p⌋ - 2 ∑_{i=1}^{h-1} ⌊2i/p⌋`. -/
theorem padicValRat_scalingFactor_of_sq_gt {n p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : 2 * poleBound n < p ^ 2) :
    padicValRat p (scalingFactor n) =
      2 * matrixOrder n * (poleBound n / p : ℕ) - 12 * matrixOrder n * (innerDegree n / p : ℕ) -
        2 * ∑ i ∈ Icc 1 (matrixOrder n - 1), (2 * i / p : ℕ) := by
  have hK1 : poleBound n < p ^ 2 := by omega
  have hN := finsum_mem_Ici_one_div_pow_eq_div (p := p) (m := innerDegree n)
    (lt_of_le_of_lt (innerDegree_le_poleBound n) hK1)
  have hi : ∀ i ∈ Icc 1 (matrixOrder n - 1),
      ∑ᶠ a ∈ Set.Ici 1, 2 * i / p ^ a = 2 * i / p := by
    intro i hi
    rw [mem_Icc] at hi
    refine finsum_mem_Ici_one_div_pow_eq_div ?_
    simp only [matrixOrder, poleBound] at hi hK
    omega
  have h4 : padicValNat p 4 = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun h => hp2 ?_
    have h22 : p ∣ 2 ^ 2 := by norm_num; exact h
    exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h22)
  rw [padicValRat_scalingFactor, finsum_mem_Ici_one_div_pow_eq_div hK1, hN, sum_congr rfl hi, h4]
  push_cast
  ring

/-- For a prime `p` with `K < 3p` and `p ≤ 2h`, the valuation of `S_K` is
`v_p(S_K) = 2h ⌊K/p⌋ - 2 ∑_{j=1}^{5} (h - ⌈jp/2⌉)₊`, with `⌈jp/2⌉ = ⌊(jp + 1)/2⌋`. -/
theorem padicValRat_scalingFactor_of_lt {n p : ℕ} [hp : Fact p.Prime]
    (hpK : poleBound n < 3 * p) (hph : p ≤ 2 * matrixOrder n) :
    padicValRat p (scalingFactor n) =
      2 * matrixOrder n * (poleBound n / p : ℕ) -
        2 * ∑ j ∈ Icc 1 5, (matrixOrder n - (j * p + 1) / 2 : ℕ) := by
  have hp2 := hp.out.two_le
  have hpne : p ≠ 2 := by
    rintro rfl; simp only [poleBound, matrixOrder] at hpK hph; omega
  have hsq : 2 * poleBound n < p ^ 2 := by
    simp only [poleBound, matrixOrder] at hpK hph ⊢
    have := Nat.mul_self_lt_mul_self hpK
    have hn : 1 ≤ n := by omega
    nlinarith
  rw [padicValRat_scalingFactor_of_sq_gt hpne hsq]
  simp only [poleBound, matrixOrder] at hpK hph ⊢
  have hN : innerDegree n / p = 0 := Nat.div_eq_of_lt (by simp only [innerDegree]; omega)
  have hcount := Nat.sum_Icc_two_mul_div_eq_sum_Icc hp.out.pos (37 * n - 1)
  rw [Nat.sub_add_cancel (by omega)] at hcount
  have hk : 2 * (37 * n - 1) / p ≤ 5 := by
    rw [Nat.div_le_iff_le_mul_add_pred hp.out.pos]; omega
  have hext : ∑ j ∈ Icc 1 (2 * (37 * n - 1) / p), (37 * n - (j * p + 1) / 2) =
      ∑ j ∈ Icc 1 5, (37 * n - (j * p + 1) / 2) := by
    apply sum_subset (Icc_subset_Icc_right hk)
    intro j hj5 hjk
    simp only [mem_Icc, not_and, not_le] at hj5 hjk
    have := Nat.lt_mul_div_succ (2 * (37 * n - 1)) hp.out.pos
    have : p * (2 * (37 * n - 1) / p + 1) ≤ p * j := Nat.mul_le_mul_left _ (hjk hj5.1)
    have := Nat.mul_comm j p
    omega
  rw [hN, hcount, hext]
  push_cast
  ring

/-- One term of the outer estimate: with `h = λ K`,
`|2 (h - ⌈m/2⌉)₊ - K (2λ - m/K)₊| ≤ 1`. -/
theorem abs_two_mul_sub_ceil_sub_mul_posPart_le {K lam : ℝ} (hK : 0 < K) {h m : ℕ}
    (hh : (h : ℝ) = lam * K) :
    |2 * ((h - (m + 1) / 2 : ℕ) : ℝ) - K * (2 * lam - m / K)⁺| ≤ 1 := by
  have hKx : K * (2 * lam - m / K) = 2 * h - m := by
    rw [hh]; field_simp
  rw [posPart_def, mul_max_of_nonneg _ _ hK.le, mul_zero, hKx]
  obtain ⟨q, hq⟩ : ∃ q, (m + 1) / 2 = q := ⟨_, rfl⟩
  have h1 : 2 * q ≤ m + 1 := by omega
  have h2 : m ≤ 2 * q := by omega
  rw [hq]
  rcases lt_or_ge m (2 * h) with hm | hm
  · have hqh : q ≤ h := by omega
    have hm' : (m : ℝ) ≤ 2 * h := by exact_mod_cast hm.le
    have h1' : (2 * q : ℝ) ≤ m + 1 := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ 2 * q := by exact_mod_cast h2
    rw [max_eq_left (by linarith), Nat.cast_sub hqh, abs_le]
    constructor <;> linarith
  · have hm' : (2 * h : ℝ) ≤ m := by exact_mod_cast hm
    rw [max_eq_right (by linarith), Nat.sub_eq_zero_of_le (by omega)]
    norm_num

/-- **The outer estimate for `v_p(S_K)`.** For every prime `p` with `K/3 < p ≤ 2h`,
`|-v_p(S_K) - K (-2λ ⌊K/p⌋ + ∑_{j=1}^{5} (2λ - j p / K)₊)| ≤ 20`.
The source additionally assumes `K ≥ 200 M²` for an integer `M ≥ 40`; this is not needed. -/
@[zeta5irr "lem_norm_vpSK_outer"]
theorem abs_neg_padicValRat_scalingFactor_sub_le {n p : ℕ} (hp : p.Prime)
    (hpK : (poleBound n : ℝ) / 3 < p) (hph : p ≤ 2 * matrixOrder n) :
    |-(padicValRat p (scalingFactor n) : ℝ) -
        poleBound n * (-2 * (orderRatio : ℝ) * ⌊(poleBound n : ℝ) / p⌋ +
          ∑ j ∈ Icc (1 : ℕ) 5, (2 * (orderRatio : ℝ) - j * p / poleBound n)⁺)| ≤ 20 := by
  have := Fact.mk hp
  have hpK' : poleBound n < 3 * p := by
    have : (poleBound n : ℝ) < 3 * p := by linarith
    exact_mod_cast this
  have hn : 0 < n := by simp only [matrixOrder] at hph; have := hp.two_le; omega
  have hK : (0 : ℝ) < poleBound n := by exact_mod_cast poleBound_pos hn
  have hh : (matrixOrder n : ℝ) = orderRatio * poleBound n := by
    simp only [matrixOrder, poleBound, orderRatio]; push_cast; ring
  have hfloor : ⌊(poleBound n : ℝ) / p⌋ = ((poleBound n / p : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  rw [padicValRat_scalingFactor_of_lt hpK' hph, hfloor]
  generalize poleBound n / p = q
  push_cast
  have key : -(2 * (matrixOrder n : ℝ) * (q : ℝ) -
        2 * ∑ j ∈ Icc 1 5, ((matrixOrder n - (j * p + 1) / 2 : ℕ) : ℝ)) -
      poleBound n * (-2 * (orderRatio : ℝ) * (q : ℝ) +
        ∑ j ∈ Icc (1 : ℕ) 5, (2 * (orderRatio : ℝ) - j * p / poleBound n)⁺) =
      ∑ j ∈ Icc 1 5, (2 * ((matrixOrder n - (j * p + 1) / 2 : ℕ) : ℝ) -
        poleBound n * (2 * (orderRatio : ℝ) - j * p / poleBound n)⁺) := by
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hh]
    ring
  rw [key]
  calc _ ≤ ∑ j ∈ Icc 1 5, (1 : ℝ) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
        have := abs_two_mul_sub_ceil_sub_mul_posPart_le hK hh (m := j * p)
        push_cast at this
        exact this
    _ ≤ 20 := by norm_num

end Zeta5Irr
