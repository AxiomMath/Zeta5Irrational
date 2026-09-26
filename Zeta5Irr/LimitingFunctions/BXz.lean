/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LimitingFunctions.EllXz

/-!
# The weighted pole count `b(x, z)`

The weighted pole count is `b(x, z) = 3 ℓ(α x, z)`, where `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`
is the pole count and `α = 3/40` is the inner ratio. It enters the inner limiting function
`Γ` through the integrand `(T̃(x) - b(x, z)) (T̃(x) + b(x, z) - ℓ(x, z) - 5)` over
`0 ≤ z ≤ 1/2`.

## Main definitions

* `Zeta5Irr.weightedPoleCount`: the function `b(x, z) = 3 ℓ(α x, z)`.

## Main results

* `Zeta5Irr.weightedPoleCount_zero_right`: `b(x, 0) = 3 (2 ⌊α x⌋ + 1)`.
* `Zeta5Irr.weightedPoleCount_neg_right`: `b(x, -z) = b(x, z)`.
* `Zeta5Irr.weightedPoleCount_le`, `Zeta5Irr.lt_weightedPoleCount`:
  `6 α x - 3 < b(x, z) ≤ 6 α x + 3`.

## Implementation notes

* The source states the definition for `x ≥ 3` and `0 ≤ z ≤ 1/2`. The formula makes sense
  for all real `x` and `z`, so `b` is defined on `ℝ × ℝ`; this keeps it usable as an
  integrand in `z` without restricting to a subtype. The constraints are hypotheses of the
  lemmas that need them; none of the lemmas in this file need them.
* `b` is real-valued, the coercion of the integer `3 ℓ(α x, z)`, because it is always
  combined with real quantities.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The weighted pole count `b(x, z) = 3 ℓ(α x, z)`, with `α = 3/40` the inner ratio.
The source restricts to `x ≥ 3` and `0 ≤ z ≤ 1/2`; the formula is used for all real `x`
and `z`. -/
@[zeta5irr "def_b_xz"]
noncomputable def weightedPoleCount (x z : ℝ) : ℝ := 3 * ell ((innerRatio : ℝ) * x) z

/-- Unfolding lemma for `b`. -/
theorem weightedPoleCount_def (x z : ℝ) :
    weightedPoleCount x z = 3 * ell ((innerRatio : ℝ) * x) z := rfl

/-- `b(x, 0) = 3 (2 ⌊α x⌋ + 1)`. -/
@[simp]
theorem weightedPoleCount_zero_right (x : ℝ) :
    weightedPoleCount x 0 = 3 * (2 * ⌊(innerRatio : ℝ) * x⌋ + 1) := by
  simp [weightedPoleCount_def]

/-- `b` is even in `z`: `b(x, -z) = b(x, z)`. -/
theorem weightedPoleCount_neg_right (x z : ℝ) :
    weightedPoleCount x (-z) = weightedPoleCount x z := by
  simp only [weightedPoleCount_def, ell_neg_right]

/-- `b(x, z) ≤ 6 α x + 3`. -/
theorem weightedPoleCount_le (x z : ℝ) :
    weightedPoleCount x z ≤ 6 * (innerRatio : ℝ) * x + 3 := by
  have := ell_le ((innerRatio : ℝ) * x) z
  rw [weightedPoleCount_def]
  linarith

/-- `6 α x - 3 < b(x, z)`. -/
theorem lt_weightedPoleCount (x z : ℝ) :
    6 * (innerRatio : ℝ) * x - 3 < weightedPoleCount x z := by
  have := lt_ell ((innerRatio : ℝ) * x) z
  rw [weightedPoleCount_def]
  linarith

end Zeta5Irr
