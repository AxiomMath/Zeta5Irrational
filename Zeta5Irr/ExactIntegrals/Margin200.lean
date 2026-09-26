/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.AM
public import Zeta5Irr.ExactIntegrals.U

/-!
# The final rational margin at mesh `M = 200`

With `λ = 37/40`, the margin at mesh `200` is
`A_200 = A_* + 259/8000 - 2863/9600000 + 1/250000
  = 127125602969131786927559 / 94195881588024216000000`,
and adding the energy margin `U = -2733991/2000000` gives
`A_200 + U = -1639743280230170235469 / 94195881588024216000000 < 0`. Consequently
`-1600 (A_200 + U) = 1639743280230170235469 / 58872425992515135000 > 139/5`.

## Main results

* `Zeta5Irr.AM_two_hundred_add_energyMargin`: the exact value of `A_200 + U`.
* `Zeta5Irr.lt_neg_mul_AM_two_hundred_add_energyMargin`: `139/5 < -1600 (A_200 + U)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.5 (the final rational margin).
-/

@[expose] public section

namespace Zeta5Irr

/-- The exact value
`A_200 + U = -1639743280230170235469 / 94195881588024216000000`. -/
theorem AM_two_hundred_add_energyMargin :
    AM 200 + energyMargin = -1639743280230170235469 / 94195881588024216000000 := by
  rw [AM, energyMargin_eq, Astar, orderRatio]
  norm_num

/-- The final rational margin at mesh `200`: `-1600 (A_200 + U) > 139/5`. -/
@[zeta5irr "lem_margin_200"]
theorem lt_neg_mul_AM_two_hundred_add_energyMargin :
    139 / 5 < -1600 * (AM 200 + energyMargin) := by
  rw [AM_two_hundred_add_energyMargin]
  norm_num

end Zeta5Irr
