/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Qx

/-!
# The limiting offset at the base `ñ`

The limiting offset at the base is `ñ(x) = (2 x - q̃(x)) / 2`, where `q̃(x) = ⌊2 x⌋` is the
limiting pole count at the base. Equivalently `ñ(x)` is half the fractional part of `2 x`, the
distance from `x` down to the nearest half-integer. It enters the functional `Γ` through the
positive part `(s̃(x) - ñ(x))₊`.

## Main definitions

* `Zeta5Irr.baseHalfFract`: the limiting offset at the base `ñ(x) = (2 x - q̃(x)) / 2`.

## Main results

* `Zeta5Irr.baseHalfFract_eq_fract`: `ñ(x) = fract(2 x) / 2`.
* `Zeta5Irr.baseHalfFract_nonneg`, `Zeta5Irr.baseHalfFract_lt_half`: `0 ≤ ñ(x) < 1 / 2`.

## Implementation notes

* The source defines `ñ` only for `x ≥ 3`. The formula makes sense for every real `x`, so
  `ñ` is defined on all of `ℝ`, and the restriction `x ≥ 3` is carried by the lemmas that
  use it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The limiting offset at the base `ñ(x) = (2 x - q̃(x)) / 2`, half the fractional part of
`2 x`. The source restricts to `x ≥ 3`; the formula is used for all real `x`. -/
@[zeta5irr "def_nplus"]
noncomputable def baseHalfFract (x : ℝ) : ℝ := (2 * x - basePoleCount x) / 2

/-- Unfolding lemma for `ñ`. -/
theorem baseHalfFract_def (x : ℝ) : baseHalfFract x = (2 * x - basePoleCount x) / 2 := rfl

/-- `ñ(x)` is half the fractional part of `2 x`. -/
theorem baseHalfFract_eq_fract (x : ℝ) : baseHalfFract x = Int.fract (2 * x) / 2 := rfl

/-- `0 ≤ ñ(x)`. -/
theorem baseHalfFract_nonneg (x : ℝ) : 0 ≤ baseHalfFract x := by
  rw [baseHalfFract_eq_fract]; exact div_nonneg (Int.fract_nonneg _) zero_le_two

/-- `ñ(x) < 1 / 2`. -/
theorem baseHalfFract_lt_half (x : ℝ) : baseHalfFract x < 1 / 2 := by
  rw [baseHalfFract_eq_fract]; linarith [Int.fract_lt_one (2 * x)]

end Zeta5Irr
