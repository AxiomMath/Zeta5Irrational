/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The outer limiting function `R₀`

The outer limiting function is the piecewise-linear function of `y ≥ 1/3` given by
* `R₀(y) = 8 - 9 y - 8 α - 5 min(α, 1 - 2 y) - 5 (1 + α - 3 y)⁺` for `1/3 ≤ y ≤ 1/2`,
* `R₀(y) = 7 (1 - y) - 6 min(α, 1 - y) - 6 (1 + α - 2 y)⁺ + (1 + 4 α - 2 y)⁺` for
  `1/2 < y ≤ 1`,
* `R₀(y) = 0` for `y > 1`,

where `α = 3/40` is the inner ratio and `(·)⁺` is the positive part.

## Main definitions

* `Zeta5Irr.outerLimitingFunction`: the function `R₀`.

## Main results

* `Zeta5Irr.outerLimitingFunction_of_le_half`,
  `Zeta5Irr.outerLimitingFunction_of_half_lt_of_le_one`,
  `Zeta5Irr.outerLimitingFunction_of_one_lt`: the value of `R₀` on each of the three ranges.

## Implementation notes

* The source defines `R₀` only for `y ≥ 1/3`. The first formula makes sense for every real
  `y`, so `R₀` is defined on all of `ℝ` by using it for every `y ≤ 1/2`; the restriction
  `y ≥ 1/3` is carried by the lemmas that use it.
* The positive part is Mathlib's `PosPart.posPart`, written `a⁺ = a ⊔ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.2: the outer limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The outer limiting function `R₀`, with `α = 3/40` the inner ratio:
`R₀(y) = 8 - 9 y - 8 α - 5 min(α, 1 - 2 y) - 5 (1 + α - 3 y)⁺` for `y ≤ 1/2`,
`R₀(y) = 7 (1 - y) - 6 min(α, 1 - y) - 6 (1 + α - 2 y)⁺ + (1 + 4 α - 2 y)⁺` for
`1/2 < y ≤ 1`, and `R₀(y) = 0` for `y > 1`. The source restricts to `y ≥ 1/3`. -/
@[zeta5irr "def_R0"]
noncomputable def outerLimitingFunction (y : ℝ) : ℝ :=
  if y ≤ 1 / 2 then
    8 - 9 * y - 8 * (innerRatio : ℝ) - 5 * min (innerRatio : ℝ) (1 - 2 * y) -
      5 * (1 + (innerRatio : ℝ) - 3 * y)⁺
  else if y ≤ 1 then
    7 * (1 - y) - 6 * min (innerRatio : ℝ) (1 - y) - 6 * (1 + (innerRatio : ℝ) - 2 * y)⁺ +
      (1 + 4 * (innerRatio : ℝ) - 2 * y)⁺
  else 0

/-- `R₀(y) = 8 - 9 y - 8 α - 5 min(α, 1 - 2 y) - 5 (1 + α - 3 y)⁺` for `y ≤ 1/2`. -/
theorem outerLimitingFunction_of_le_half {y : ℝ} (hy : y ≤ 1 / 2) :
    outerLimitingFunction y =
      8 - 9 * y - 8 * (innerRatio : ℝ) - 5 * min (innerRatio : ℝ) (1 - 2 * y) -
        5 * (1 + (innerRatio : ℝ) - 3 * y)⁺ := by
  rw [outerLimitingFunction, ite_eq_left hy]

/-- `R₀(y) = 7 (1 - y) - 6 min(α, 1 - y) - 6 (1 + α - 2 y)⁺ + (1 + 4 α - 2 y)⁺` for
`1/2 < y ≤ 1`. -/
theorem outerLimitingFunction_of_half_lt_of_le_one {y : ℝ} (hy₁ : 1 / 2 < y) (hy₂ : y ≤ 1) :
    outerLimitingFunction y =
      7 * (1 - y) - 6 * min (innerRatio : ℝ) (1 - y) -
        6 * (1 + (innerRatio : ℝ) - 2 * y)⁺ + (1 + 4 * (innerRatio : ℝ) - 2 * y)⁺ := by
  rw [outerLimitingFunction, ite_eq_right hy₁.not_ge, ite_eq_left hy₂]

/-- `R₀(y) = 0` for `y > 1`. -/
theorem outerLimitingFunction_of_one_lt {y : ℝ} (hy : 1 < y) : outerLimitingFunction y = 0 := by
  rw [outerLimitingFunction, ite_eq_right (by linarith), ite_eq_right hy.not_ge]

end Zeta5Irr
