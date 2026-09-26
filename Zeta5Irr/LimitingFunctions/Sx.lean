/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Tx

/-!
# The allocation remainder `s̃`

The allocation remainder is `s̃(x) = H x - T̃(x) / 2`, where `H = 23/20` is the height ratio
and `T̃(x) = ⌊2 H x⌋` is the base allocation. Since `T̃(x)` is the integer part of `2 H x`,
the remainder is half the fractional part of `2 H x`, so it lies in `[0, 1/2)`.

## Main definitions

* `Zeta5Irr.allocationRemainder`: the allocation remainder `s̃(x) = H x - T̃(x) / 2`.

## Main results

* `Zeta5Irr.allocationRemainder_eq_half_fract`: `s̃(x) = fract(2 H x) / 2`.

## Implementation notes

* The source defines `s̃` only for `x ≥ 3`. The formula makes sense for every real `x`, so
  `s̃` is defined on all of `ℝ`; none of the lemmas below needs the restriction.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The allocation remainder `s̃(x) = H x - T̃(x) / 2`, where `H = 23/20` is the height ratio
and `T̃` is the base allocation `Zeta5Irr.innerLimit`. The source restricts to `x ≥ 3`; the
formula is used for all real `x`. -/
@[zeta5irr "def_sx"]
noncomputable def allocationRemainder (x : ℝ) : ℝ := (heightRatio : ℝ) * x - innerLimit x / 2

/-- `s̃(x) = H x - T̃(x) / 2`. -/
theorem allocationRemainder_def (x : ℝ) :
    allocationRemainder x = (heightRatio : ℝ) * x - innerLimit x / 2 := rfl

/-- `s̃(x)` is half the fractional part of `2 H x`. -/
theorem allocationRemainder_eq_half_fract (x : ℝ) :
    allocationRemainder x = Int.fract (2 * (heightRatio : ℝ) * x) / 2 := by
  rw [allocationRemainder_def, innerLimit_def, Int.fract]
  ring

end Zeta5Irr
