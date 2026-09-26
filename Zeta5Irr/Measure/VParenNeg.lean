/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Measure.VQpmNotation
public import Zeta5Irr.Measure.EncAtanSpec
public import Zeta5Irr.Measure.EncAtanHalf
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The bracket in the floor of the external field is negative

With `α = 3/40`, `q₋ = 59205077 / 10¹⁰` and `q₊ = 59205079 / 10¹⁰`,
`π + arctan (1 / √q₊) - 6 arctan (α / √q₋) < 0`.

Each summand is enclosed by rationals. By `Real.arctan_inv_of_pos`,
`arctan (1 / √q₊) = π/2 - arctan √q₊`, and `arctan √q₊ ≥ arctan a` for a rational `a ≤ √q₊`.
For the second arctangent, `arctan (α / √q₋) ≥ arctan r` for a rational `r ≤ α / √q₋`, and the
half-angle formula `arctan r = 2 arctan (r / (1 + √(1 + r²)))` together with a rational
`c ≥ √(1 + r²)` reduces it to an arctangent at a rational argument `u ≤ r / (1 + c)` near
`0.41`. Both remaining arctangents at rationals are bounded below by the truncated Taylor
series minus its alternating-series error, and `π` is bounded above by `Real.pi_lt_d20`. The
resulting rational upper bound is about `-2.4995 × 10⁻⁸`.

## Main results

* `Zeta5Irr.pi_add_arctan_sub_six_mul_arctan_neg`:
  `π + arctan (1 / √q₊) - 6 arctan (α / √q₋) < 0`.

## Implementation notes

* The source encloses `π` through Machin's formula and the square roots through the dyadic
  enclosure `s(x)`, with `80` terms of the arctangent series. Here `π` is bounded by
  `Real.pi_lt_d20`, the square roots by explicit decimals with twelve digits whose squares are
  compared directly, and the arctangent series is truncated after `5` and `14` terms; only
  the ends of the brackets that give an upper bound are used.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6 (The interval bound and the partition of `[0,2]`).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The bracket in the floor of the external field is negative:
`π + arctan (1 / √q₊) - 6 arctan (α / √q₋) < 0`, with `α = 3/40`, `q₋ = 59205077 / 10¹⁰` and
`q₊ = 59205079 / 10¹⁰`. -/
@[zeta5irr "lem_V_paren_neg"]
theorem pi_add_arctan_sub_six_mul_arctan_neg :
    π + arctan (1 / √(externalFieldMinUpper : ℝ)) -
      6 * arctan ((innerRatio : ℝ) / √(externalFieldMinLower : ℝ)) < 0 := by
  rw [externalFieldMinUpper, externalFieldMinLower, innerRatio]
  push_cast
  set a : ℝ := 76944836733 / 1000000000000
  set r : ℝ := 974724288859 / 1000000000000
  set c : ℝ := 279291062463 / 200000000000
  set u : ℝ := 203367925087 / 500000000000
  -- the first arctangent
  have hqp : 0 < √((59205079 : ℝ) / 10 ^ 10) := Real.sqrt_pos.2 (by norm_num)
  have ha : a ≤ √((59205079 : ℝ) / 10 ^ 10) := Real.le_sqrt_of_sq_le (by norm_num [a])
  have h1 : arctan (1 / √((59205079 : ℝ) / 10 ^ 10)) ≤ π / 2 - arctan a := by
    rw [one_div, arctan_inv_of_pos hqp]
    linarith [arctan_mono ha]
  have h1' := atanApprox_sub_le_arctan (z := a) (by norm_num [a]) (by norm_num [a]) 5
  -- the second arctangent
  have hqm : 0 < √((59205077 : ℝ) / 10 ^ 10) := Real.sqrt_pos.2 (by norm_num)
  have hr : r ≤ 3 / 40 / √((59205077 : ℝ) / 10 ^ 10) := by
    rw [le_div_iff₀ hqm]
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 59205077 / 10 ^ 10 by norm_num)
    have : (r * √((59205077 : ℝ) / 10 ^ 10)) ^ 2 ≤ (3 / 40) ^ 2 := by
      rw [mul_pow, hsq]; norm_num [r]
    exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 this
  have hc : √(1 + r ^ 2) ≤ c := by
    rw [Real.sqrt_le_iff]; norm_num [r, c]
  have hu : u ≤ r / (1 + √(1 + r ^ 2)) := by
    calc u ≤ r / (1 + c) := by norm_num [u, r, c]
      _ ≤ r / (1 + √(1 + r ^ 2)) := by gcongr
  have h2 : 2 * arctan u ≤ arctan (3 / 40 / √((59205077 : ℝ) / 10 ^ 10)) := by
    calc 2 * arctan u ≤ 2 * arctan (r / (1 + √(1 + r ^ 2))) := by gcongr
      _ = arctan r := (arctan_eq_two_mul_arctan_div_one_add_sqrt r).symm
      _ ≤ _ := arctan_mono hr
  have h2' := atanApprox_sub_le_arctan (z := u) (by norm_num [u]) (by norm_num [u]) 14
  have hpi := Real.pi_lt_d20
  have key : (314159265358979323847 / 10 ^ 20 : ℝ) + 314159265358979323847 / 10 ^ 20 / 2 -
      (atanApprox 5 a - a ^ (2 * 5 + 1) / (2 * 5 + 1)) -
      12 * (atanApprox 14 u - u ^ (2 * 14 + 1) / (2 * 14 + 1)) < 0 := by
    simp only [a, u, atanApprox, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  push_cast at h1' h2'
  norm_num at hpi
  linarith

end Zeta5Irr
