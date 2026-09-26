/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormDelta
public import Zeta5Irr.PrimeSum.NormEllStep

/-!
# The deviation `δ(x, z)` as a step function

For real `x` and `0 < z < 1/2`, the deviation `δ(x, z) = ℓ(x, z) - 2x` equals
`𝟙_{S(x)}(z) - {2x}`, where `S(x)` is the step set. This follows from
`ℓ(x, z) = ⌊2x⌋ + 𝟙_{S(x)}(z)` and `2x - ⌊2x⌋ = {2x}`.

## Main results

* `Zeta5Irr.ellDeviation_eq_indicator_sub_fract`: `δ(x, z) = 𝟙_{S(x)}(z) - {2x}` for
  `0 < z < 1/2`.

## Implementation notes

* The indicator is `Set.indicator (normUpperSet x) 1 z`, valued in `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2 (The step structure of the pole counts).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `0 < z < 1/2`, `δ(x, z) = 𝟙_{S(x)}(z) - {2x}`. -/
@[zeta5irr "lem_norm_delta_formula"]
theorem ellDeviation_eq_indicator_sub_fract (x : ℝ) {z : ℝ} (hz₀ : 0 < z) (hz₁ : z < 1 / 2) :
    ellDeviation x z = (normUpperSet x).indicator 1 z - Int.fract (2 * x) := by
  rw [ellDeviation_def, ell_eq_floor_two_mul_add_indicator x hz₀ hz₁, ← Int.self_sub_floor]
  by_cases h : z ∈ normUpperSet x
  · simp only [Set.indicator_of_mem h, Pi.one_apply]; push_cast; ring
  · simp only [Set.indicator_of_notMem h]; push_cast; ring

end Zeta5Irr
