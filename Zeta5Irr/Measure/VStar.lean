/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Measure.VQpmNotation

/-!
# The floor `V_*` of the external field

For `t > 0` the external field has the closed form
`V(t) = log (1 + t) - 6 α log (t + α²) - 2 + 12 α + 2 √t (π + arctan (1/√t) - 6 arctan (α/√t))`.
Bounding each factor in the direction that decreases it for `q₋ ≤ t ≤ q₊` gives the constant
`V_* = log (1 + q₋) - 6 α log (q₊ + α²) - 2 + 12 α
  + 2 √q₊ (π + arctan (1/√q₊) - 6 arctan (α/√q₋))`,
where `α = 3/40` and `q₋ < q₊` bracket the minimum of `V`. It is the value subtracted in the
interval bound on the cells of the partition of `[0, 2]` that meet `[q₋, q₊]`.

## Main definitions

* `Zeta5Irr.externalFieldFloor`: the constant `V_*`.

## Main results

* `Zeta5Irr.externalFieldFloor_eq`: `V_*` with `α`, `q₋` and `q₊` substituted.

## Implementation notes

* The source's name `V_*` is not an identifier; the constant is named for its role as a floor
  of the external field. The rational constants `α`, `q₋`, `q₊` are coerced to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6 (equation (A.6)): the interval bound and the
  partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The floor
`V_* = log (1 + q₋) - 6 α log (q₊ + α²) - 2 + 12 α
  + 2 √q₊ (π + arctan (1/√q₊) - 6 arctan (α/√q₋))`
of the external field on `[q₋, q₊]`, where `α = 3/40` is `Zeta5Irr.innerRatio` and
`q₋`, `q₊` are `Zeta5Irr.externalFieldMinLower`, `Zeta5Irr.externalFieldMinUpper`. -/
@[zeta5irr "def_V_star"]
noncomputable def externalFieldFloor : ℝ :=
  log (1 + (externalFieldMinLower : ℝ)) -
      6 * (innerRatio : ℝ) * log ((externalFieldMinUpper : ℝ) + (innerRatio : ℝ) ^ 2) - 2 +
    12 * (innerRatio : ℝ) +
    2 * √(externalFieldMinUpper : ℝ) *
      (π + arctan (√(externalFieldMinUpper : ℝ))⁻¹ -
        6 * arctan ((innerRatio : ℝ) / √(externalFieldMinLower : ℝ)))

/-- The floor `V_*` with `α = 3/40`, `q₋ = 59205077 / 10¹⁰` and `q₊ = 59205079 / 10¹⁰`
substituted. -/
theorem externalFieldFloor_eq :
    externalFieldFloor =
      log (1 + 59205077 / 10 ^ 10) - 9 / 20 * log (59205079 / 10 ^ 10 + 9 / 1600) - 2 +
        9 / 10 +
      2 * √(59205079 / 10 ^ 10) *
        (π + arctan (√(59205079 / 10 ^ 10))⁻¹ -
          6 * arctan (3 / 40 / √(59205077 / 10 ^ 10))) := by
  rw [externalFieldFloor, innerRatio, externalFieldMinLower, externalFieldMinUpper]
  push_cast
  norm_num

end Zeta5Irr
