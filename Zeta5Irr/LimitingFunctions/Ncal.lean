/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LimitingFunctions.J

/-!
# The scalar limiting function `𝒩`

For `x ≥ 3` the scalar limiting function is
`𝒩(x) = 2 λ x ⌊x⌋ - 12 λ x ⌊α x⌋ - 2 𝒥(λ x)`,
where `α = 3/40` and `λ = 37/40` are the ratios of the construction and `𝒥` is the
floor-sum function. Between consecutive jumps of the floors `⌊x⌋`, `⌊α x⌋` and `⌊2 λ x⌋`
it is an affine function of `x`, with coefficients determined by the three floor values.

## Main definitions

* `Zeta5Irr.scalarLimitingFunction`: the function `𝒩`.

## Main results

* `Zeta5Irr.scalarLimitingFunction_eq`: the formula with the values of `α` and `λ`
  substituted.
* `Zeta5Irr.scalarLimitingFunction_of_floor_eq`: if `⌊x⌋ = a`, `⌊α x⌋ = b` and
  `⌊2 λ x⌋ = c`, then `𝒩(x) = 2 λ a x - 12 λ b x - 2 (c λ x - c (c + 1) / 4)`.

## Implementation notes

* The source defines `𝒩` only for `x ≥ 3`. The formula makes sense for every real `x`, so
  `𝒩` is defined on all of `ℝ`, and the restriction `x ≥ 3` is carried by the lemmas that
  use it.
* The source's letter `𝒩` is not the inner degree `N = 3 n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the scalar limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The scalar limiting function `𝒩(x) = 2 λ x ⌊x⌋ - 12 λ x ⌊α x⌋ - 2 𝒥(λ x)`, where
`α = 3/40` is the inner ratio, `λ = 37/40` the order ratio and `𝒥` the floor-sum function.
The source restricts to `x ≥ 3`; the formula is used for all real `x`. -/
@[zeta5irr "def_Ncal"]
noncomputable def scalarLimitingFunction (x : ℝ) : ℝ :=
  2 * (orderRatio : ℝ) * x * ⌊x⌋ - 12 * (orderRatio : ℝ) * x * ⌊(innerRatio : ℝ) * x⌋ -
    2 * innerLimitingFunction ((orderRatio : ℝ) * x)

/-- `𝒩(x) = 2 λ x ⌊x⌋ - 12 λ x ⌊α x⌋ - 2 𝒥(λ x)`. -/
theorem scalarLimitingFunction_def (x : ℝ) :
    scalarLimitingFunction x =
      2 * (orderRatio : ℝ) * x * ⌊x⌋ - 12 * (orderRatio : ℝ) * x * ⌊(innerRatio : ℝ) * x⌋ -
        2 * innerLimitingFunction ((orderRatio : ℝ) * x) :=
  rfl

/-- `𝒩(x) = (37/20) x ⌊x⌋ - (111/10) x ⌊3 x / 40⌋ - 2 𝒥(37 x / 40)`, with the values of
`α` and `λ` substituted. -/
theorem scalarLimitingFunction_eq (x : ℝ) :
    scalarLimitingFunction x =
      37 / 20 * x * ⌊x⌋ - 111 / 10 * x * ⌊3 / 40 * x⌋ -
        2 * innerLimitingFunction (37 / 40 * x) := by
  rw [scalarLimitingFunction_def]
  norm_num [orderRatio, innerRatio]

/-- If `⌊x⌋ = a`, `⌊α x⌋ = b` and `⌊2 λ x⌋ = c`, then
`𝒩(x) = 2 λ a x - 12 λ b x - 2 (c λ x - c (c + 1) / 4)`: on each interval where the three
floors are constant, `𝒩` is affine in `x`. -/
theorem scalarLimitingFunction_of_floor_eq {x : ℝ} {a b c : ℤ} (ha : ⌊x⌋ = a)
    (hb : ⌊(innerRatio : ℝ) * x⌋ = b) (hc : ⌊2 * ((orderRatio : ℝ) * x)⌋ = c) :
    scalarLimitingFunction x =
      2 * (orderRatio : ℝ) * a * x - 12 * (orderRatio : ℝ) * b * x -
        2 * (c * ((orderRatio : ℝ) * x) - c * (c + 1) / 4) := by
  rw [scalarLimitingFunction_def, innerLimitingFunction_of_floor_eq hc, ha, hb]
  ring

end Zeta5Irr
