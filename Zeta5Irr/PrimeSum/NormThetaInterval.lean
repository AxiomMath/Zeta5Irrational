/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormThetaPnt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

/-!
# Prime sums over dilated intervals

For reals `0 ≤ u ≤ v`, the prime number theorem gives
`(1 / K) ∑_{uK < p ≤ vK} log p → v - u` as `K → ∞`. Indeed the sum is `ϑ(vK) - ϑ(uK)`, and
`ϑ(cK) / K → c` for every `c ≥ 0` because `ϑ(y) / y → 1`.

## Main results

* `Zeta5Irr.sum_Ioc_floor_prime_log_eq_theta_sub`: for `x ≤ y`, the sum of `log p` over primes
  `⌊x⌋₊ < p ≤ ⌊y⌋₊` is `ϑ(y) - ϑ(x)`.
* `Zeta5Irr.tendsto_theta_mul_div_atTop`: `ϑ(cK) / K → c` for `c ≥ 0`.
* `Zeta5Irr.tendsto_sum_Ioc_prime_log_div_atTop`: `(1 / K) ∑_{uK < p ≤ vK} log p → v - u`.

## Implementation notes

* For `uK ≥ 0` a natural number `p` satisfies `uK < p ≤ vK` exactly when
  `⌊uK⌋₊ < p ≤ ⌊vK⌋₊`, so the sum over primes in the real interval `(uK, vK]` is written as
  a sum over the primes of `Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊`.
* The source assumes `0 < u < v`; the statement here holds, with the same proof, for
  `0 ≤ u ≤ v`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.7 (The prime number theorem).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology Finset

/-- The sum of `log p` over primes `⌊x⌋₊ < p ≤ ⌊y⌋₊` is `ϑ(y) - ϑ(x)`. -/
theorem sum_Ioc_floor_prime_log_eq_theta_sub {x y : ℝ} (hxy : x ≤ y) :
    ∑ p ∈ Ioc ⌊x⌋₊ ⌊y⌋₊ with p.Prime, Real.log p = Chebyshev.theta y - Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, eq_sub_iff_add_eq, ← sum_union]
  · congr 1
    ext p
    grind [Nat.floor_le_floor (a := x) hxy]
  · grind [disjoint_left]

/-- The sum of `log p` over primes `a < p ≤ b` is at most `θ(b)`. -/
theorem sum_Ioc_prime_log_le_theta (a b : ℕ) :
    ∑ p ∈ Ioc a b with p.Prime, Real.log p ≤ Chebyshev.theta b := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  refine sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ ?_) fun p _ _ =>
    Real.log_natCast_nonneg p
  intro p hp
  simp only [mem_Ioc, mem_Icc] at hp ⊢
  omega

/-- If `|f p| ≤ C` for the primes `a < p ≤ b`, then `|∑_{a < p ≤ b} f(p) log p| ≤ C log 4 · b`,
the sum being over primes: the Chebyshev bound `θ(b) ≤ b log 4`. -/
theorem abs_sum_prime_mul_log_le {a b : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : ℕ → ℝ)
    (hf : ∀ p ∈ Ioc a b, p.Prime → |f p| ≤ C) :
    |∑ p ∈ Ioc a b with p.Prime, f p * Real.log p| ≤ C * (Real.log 4 * b) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ Ioc a b with p.Prime, |f p * Real.log p|
      ≤ ∑ p ∈ Ioc a b with p.Prime, C * Real.log p := by
        refine sum_le_sum fun p hp => ?_
        rw [mem_filter] at hp
        rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
        exact mul_le_mul_of_nonneg_right (hf p hp.1 hp.2) (Real.log_natCast_nonneg p)
    _ ≤ C * (Real.log 4 * b) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left ((sum_Ioc_prime_log_le_theta a b).trans
          (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _))) hC

/-- For `c ≥ 0`, `ϑ(cK) / K → c` as `K → ∞`. -/
theorem tendsto_theta_mul_div_atTop {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun K : ℝ ↦ Chebyshev.theta (c * K) / K) atTop (𝓝 c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [Chebyshev.theta_eq_sum_Icc, filter_singleton, Nat.not_prime_zero]
  · have h := (tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop hc)).const_mul c
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with K hK
    simp only [Function.comp_apply, id]
    field_simp

/-- For reals `0 ≤ u ≤ v`, `(1 / K) ∑_{uK < p ≤ vK} log p → v - u` as `K → ∞`, the sum being
over primes. -/
@[zeta5irr "lem_norm_theta_interval"]
theorem tendsto_sum_Ioc_prime_log_div_atTop {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Tendsto (fun K : ℝ ↦ (∑ p ∈ Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime, Real.log p) / K) atTop
      (𝓝 (v - u)) := by
  refine ((tendsto_theta_mul_div_atTop (hu.trans huv)).sub
    (tendsto_theta_mul_div_atTop hu)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with K hK
  rw [sum_Ioc_floor_prime_log_eq_theta_sub (mul_le_mul_of_nonneg_right huv hK), sub_div]

end Zeta5Irr
