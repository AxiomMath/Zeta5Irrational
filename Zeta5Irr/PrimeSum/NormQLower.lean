/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormEcal
public import Zeta5Irr.PrimeSum.NormNumeratorBound
public import Zeta5Irr.PrimeSum.NormDeltaProdUpper

/-!
# A lower bound for the error term `𝓔`

The error term `𝓔(x)` of the splitting of the inner limiting function satisfies
`𝓔(x) ≥ -1/2`. Its first term is half a numerator lying in `[-1/4, 1/4]`, hence at least
`-1/8`; its second term `9 ∫_0^{1/2} δ(αx, z)² dz` is nonnegative, the integrand being a
square; and its third term `-3 ∫_0^{1/2} δ(x, z) δ(αx, z) dz` is at least `-3/8`, since the
integral of a product of two deviations is at most `1/8`.

## Main results

* `Zeta5Irr.neg_half_le_innerSplitError`: `-1/2 ≤ 𝓔(x)`.

## Implementation notes

* The source states the bound for `x ≥ 3`, the range on which it defines `𝓔`. Each of the
  three estimates holds for every real `x`, so the bound is stated for all `x`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.5 (The splitting of the inner limiting function).
-/

@[expose] public section

namespace Zeta5Irr

/-- The error term of the splitting of the inner limiting function is bounded below:
`-1/2 ≤ 𝓔(x)`. The source states this for `x ≥ 3`; it holds for every real `x`. -/
@[zeta5irr "lem_norm_Q_lower"]
theorem neg_half_le_innerSplitError (x : ℝ) : -(1 / 2) ≤ innerSplitError x := by
  have h₁ := (normNumerator_bound x).1
  have h₂ : 0 ≤ ∫ z in (0 : ℝ)..(1 / 2), ellDeviation ((innerRatio : ℝ) * x) z ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun z _ => sq_nonneg _
  have h₃ := integral_ellDeviation_mul_ellDeviation_le x ((innerRatio : ℝ) * x)
  rw [innerSplitError_def]
  linarith

end Zeta5Irr
