/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.MKM
public import Zeta5Irr.PrimeSum.NormRangeSmall
public import Zeta5Irr.PrimeSum.NormRangeMid
public import Zeta5Irr.PrimeSum.NormInnerRange
public import Zeta5Irr.PrimeSum.NormOuterRange

/-!
# The growth of the normalizing factor

Let `M ≥ 40` be an integer and `K = 40 n`, `h = 37 n`, `λ = 37/40`. The logarithm of the
normalizing factor is `log m_{K,M} = -∑_{p ≤ 2h} L_p(K, M) log p`. Once `K ≥ 5 M²` one has
`√(5K) ≤ K / M ≤ K / 3 ≤ 2h`, so the primes `p ≤ 2h` split into the four ranges `p ≤ √(5K)`,
`√(5K) < p ≤ K / M`, `K / M < p ≤ K / 3` and `K / 3 < p ≤ 2h`. Divided by `K²`, the first
partial sum is `O(K^{-1/2} log (5K))`, hence tends to `0`, while the other three tend to
`6 λ / M`, `∫_3^M R(x) x⁻³ dx` and `I_out` respectively. Therefore
```
log m_{K,M} / K² → I_out + 6 λ / M + ∫_3^M R(x) / x³ dx,
```
and in particular the `limsup` of the left-hand side is at most the right-hand side.

## Main results

* `Zeta5Irr.tendsto_log_normalizingFactor_div_sq`: the limit above.
* `Zeta5Irr.limsup_log_normalizingFactor_div_sq_le`: the `limsup` bound.

## Implementation notes

* Since `K = 40 n`, the limit over `K ∈ 40 ℤ` is the limit `n → ∞`, with `K` written
  `Zeta5Irr.poleBound n`. The source's side condition `K ≥ 200 M²` holds for all large `n`,
  so it does not affect the limit and is not imposed.
* The source proves the `limsup` bound and remarks that it is an equality; the limit itself is
  proved here, and the `limsup` bound is deduced from it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8 (The growth of the normalizing factor).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology Finset

/-- `K⁻² · 15 K^{3/2} log (5K) → 0` as `K = 40 n → ∞`. -/
theorem tendsto_mul_rpow_mul_log_div_sq :
    Tendsto (fun n : ℕ => 15 * (poleBound n : ℝ) ^ (3 / 2 : ℝ) * Real.log (5 * poleBound n) /
      (poleBound n : ℝ) ^ 2) atTop (𝓝 0) := by
  have hK : Tendsto (fun n : ℕ => (5 * poleBound n : ℝ)) atTop atTop := by
    simp only [poleBound, Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hg := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
    hK).const_mul (15 * Real.sqrt 5)
  rw [mul_zero] at hg
  refine hg.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hK0 : (0 : ℝ) < poleBound n := Nat.cast_pos.2 <| by
    simp only [poleBound]
    omega
  simp only [Function.comp_apply]
  rw [Real.mul_rpow (by norm_num) hK0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hK0, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt (poleBound n : ℝ) := Real.sqrt_pos.2 hK0
  have h5 : 0 < Real.sqrt 5 := by positivity
  have hsq := Real.sq_sqrt hK0.le
  field_simp
  rw [hsq]
  ring

variable {M : ℕ}

/-- **The growth of the normalizing factor**, as a limit. For an integer `M ≥ 40`,
`log m_{K,M} / K² → I_out + 6 λ / M + ∫_3^M R(x) / x³ dx` as `K = 40 n → ∞`. -/
theorem tendsto_log_normalizingFactor_div_sq (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ => Real.log (normalizingFactor n M) / (poleBound n : ℝ) ^ 2) atTop
      (𝓝 (outerIntegral + 6 * orderRatio / M + ∫ x in (3 : ℝ)..M, innerLimitingR x / x ^ 3)) := by
  have hsmall : Tendsto (fun n : ℕ =>
      -(∑ p ∈ (Iic (Nat.sqrt (5 * poleBound n))).filter Nat.Prime,
        (localExponent n M p : ℝ) * Real.log p) / (poleBound n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_mul_rpow_mul_log_div_sq
    filter_upwards [eventually_ge_atTop (M ^ 2)] with n hn
    have hK : 5 * M ^ 2 ≤ poleBound n := by simp only [poleBound]; omega
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (sq_nonneg (poleBound n : ℝ))]
    exact div_le_div_of_nonneg_right (abs_sum_localExponent_mul_log_le hK)
      (sq_nonneg (poleBound n : ℝ))
  have hlim := (((hsmall.add (tendsto_neg_sum_localExponent_mul_log_div_sq M)).add
    (tendsto_neg_sum_inner_localExponent_mul_log_div_sq hM)).add
    (tendsto_neg_sum_outer_localExponent_mul_log_div_sq (by omega : 3 ≤ M)))
  rw [zero_add, show 6 * (orderRatio : ℝ) / M + (∫ x in (3 : ℝ)..M, innerLimitingR x / x ^ 3) +
    outerIntegral = outerIntegral + 6 * orderRatio / M +
      ∫ x in (3 : ℝ)..M, innerLimitingR x / x ^ 3 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (M ^ 2)] with n hn
  set K := poleBound n with hKdef
  have hK : 5 * M ^ 2 ≤ K := by simp only [hKdef, poleBound]; omega
  have hM0 : 0 < M := by omega
  have h1 : Nat.sqrt (5 * K) ≤ K / M := by
    rw [Nat.le_div_iff_mul_le hM0]
    refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
    nlinarith [Nat.mul_le_mul_right (M ^ 2) (Nat.sqrt_le' (5 * K)), Nat.mul_le_mul_left K hK]
  have h2 : K / M ≤ K / 3 := Nat.div_le_div_left (by omega) (by norm_num)
  have h3 : K / 3 ≤ 2 * matrixOrder n := by simp only [hKdef, poleBound, matrixOrder]; omega
  have hsplit : ∀ {a d : ℕ}, a ≤ d → ∀ f : ℕ → ℝ,
      ∑ p ∈ Iic a, f p + ∑ p ∈ Ioc a d, f p = ∑ p ∈ Iic d, f p := fun {a d} h f => by
    rw [← sum_union (disjoint_left.2 fun x hx hx' => by simp at hx hx'; omega)]
    congr 1
    ext x
    simp
    omega
  have hIoc : ∀ {a b c : ℕ}, a ≤ b → b ≤ c → ∀ f : ℕ → ℝ,
      ∑ p ∈ Ioc a b, f p + ∑ p ∈ Ioc b c, f p = ∑ p ∈ Ioc a c, f p :=
    fun h h' f => sum_Ioc_consecutive f h h'
  have hprimes : Nat.primesBelow (2 * matrixOrder n + 1) =
      (Iic (2 * matrixOrder n)).filter Nat.Prime := by
    ext p
    simp [Nat.primesBelow]
  have hfl1 : ⌊√(5 * K : ℝ)⌋₊ = Nat.sqrt (5 * K) := by
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    push_cast
    rfl
  have hfl2 : ⌊(K : ℝ) / M⌋₊ = K / M := Nat.floor_div_eq_div _ _
  rw [hfl1, hfl2, log_normalizingFactor, hprimes]
  simp only [sum_filter]
  rw [← hsplit (h1.trans (h2.trans h3)), ← hIoc h1 (h2.trans h3), ← hIoc h2 h3]
  ring

/-- **The growth of the normalizing factor.** For every integer `M ≥ 40`,
`limsup_{K → ∞, 40 ∣ K} log m_{K,M} / K² ≤ I_out + 6 λ / M + ∫_3^M R(x) / x³ dx`. -/
@[zeta5irr "prop_mKM_bound"]
theorem limsup_log_normalizingFactor_div_sq_le (hM : 40 ≤ M) :
    limsup (fun n : ℕ => Real.log (normalizingFactor n M) / (poleBound n : ℝ) ^ 2) atTop ≤
      outerIntegral + 6 * orderRatio / M + ∫ x in (3 : ℝ)..M, innerLimitingR x / x ^ 3 :=
  (tendsto_log_normalizingFactor_div_sq hM).limsup_eq.le

end Zeta5Irr
