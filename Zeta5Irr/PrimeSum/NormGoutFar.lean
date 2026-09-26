/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.R0

/-!
# The outer asymptotics away from the near range

For `1/2 < y ≤ 1`, the exponent obtained from the outer normalisation,
`7 (1 - y) - 6 min(α, 1 - y) - 6 (1 + α - 2 y)⁺ +
  min((1 + 4 α - 2 y)⁺, y - α + (1 + α - 2 y)⁺)`,
equals the outer limiting function `R₀(y)`. Indeed on this range the minimum is always its
first argument: if `y ≥ 1/2 + 2 α` then `(1 + 4 α - 2 y)⁺ = 0 < y - α`, and otherwise
`1 + 4 α - 2 y ≤ y - α` because `y > 1/2 > (1 + 5 α) / 3 = 11/24`.

## Main results

* `Zeta5Irr.outerExponent_min_eq_outerLimitingFunction`: the identity above.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.4 (The outer asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `1/2 < y ≤ 1`,
`7 (1 - y) - 6 min(α, 1 - y) - 6 (1 + α - 2 y)⁺ +
  min((1 + 4 α - 2 y)⁺, y - α + (1 + α - 2 y)⁺)`
is the outer limiting function `R₀(y)`, where `α = 3/40` is the inner ratio. -/
@[zeta5irr "lem_norm_gout_far"]
theorem outerExponent_min_eq_outerLimitingFunction {y : ℝ} (hy₁ : 1 / 2 < y) (hy₂ : y ≤ 1) :
    7 * (1 - y) - 6 * min (innerRatio : ℝ) (1 - y) - 6 * (1 + (innerRatio : ℝ) - 2 * y)⁺ +
        min (1 + 4 * (innerRatio : ℝ) - 2 * y)⁺
          (y - innerRatio + (1 + (innerRatio : ℝ) - 2 * y)⁺) =
      outerLimitingFunction y := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have h : (1 + 4 * (innerRatio : ℝ) - 2 * y)⁺ ≤
      y - innerRatio + (1 + (innerRatio : ℝ) - 2 * y)⁺ := by
    rw [hα, posPart_def, posPart_def]
    have h0 : (0 : ℝ) ≤ (1 + 3 / 40 - 2 * y) ⊔ 0 := le_max_right _ _
    exact max_le (by linarith) (by linarith)
  rw [outerLimitingFunction_of_half_lt_of_le_one hy₁ hy₂, min_eq_left h]

end Zeta5Irr
