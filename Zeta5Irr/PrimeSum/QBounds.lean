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
public import Zeta5Irr.PrimeSum.NormDeltaProdLower

/-!
# An upper bound for the error term `𝓔`

The error term `𝓔(x)` of the splitting of the inner limiting function is the sum of three
terms: half of the numerator bounded by `1/4` in absolute value, the integral
`9 ∫_0^{1/2} δ(αx, z)² dz ≤ 9/8`, and `-3 ∫_0^{1/2} δ(x, z) δ(αx, z) dz ≤ 3/8`. Adding,
`𝓔(x) ≤ 1/8 + 9/8 + 3/8 = 13/8`.

## Main results

* `Zeta5Irr.innerSplitError_le`: `𝓔(x) ≤ 13/8`.

## Implementation notes

The source states the bound for `x ≥ 3`, the range on which it defines `𝓔`. Each of the three
estimates holds for every real `x`, so the bound is stated for all `x`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.5 (The splitting of the inner limiting function).
-/

@[expose] public section

namespace Zeta5Irr

/-- **Upper bound for the error term.** For every real `x` (the source takes `x ≥ 3`),
`𝓔(x) ≤ 13/8`. -/
@[zeta5irr "lem_Q_bounds"]
theorem innerSplitError_le (x : ℝ) : innerSplitError x ≤ 13 / 8 := by
  rw [innerSplitError_def]
  have h₁ := (normNumerator_bound x).2
  have h₂ := integral_ellDeviation_mul_ellDeviation_le ((innerRatio : ℝ) * x)
    ((innerRatio : ℝ) * x)
  have h₃ := neg_one_div_eight_le_integral_ellDeviation_mul x ((innerRatio : ℝ) * x)
  simp only [← sq] at h₂
  linarith

end Zeta5Irr
