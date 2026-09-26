/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.R0
public import Zeta5Irr.LimitingFunctions.Drank

/-!
# The outer exponent on the near range

On the near range `1/3 < y ≤ 1/2`, the exponent collected from the outer block in the
asymptotics of the norm is
`7 (1 - y) - 12 α - 5 min(α, 1 - 2 y) - 5 (1 + α - 3 y)⁺
  + min(1 + 4 α - 2 y, y + (1 + α - 3 y)⁺)`,
where `α = 3/40` is the inner ratio. This file shows that it equals `R₀(y) - d_rk(y)`,
the outer limiting function corrected by the rank defect.

The proof writes `min(a, b) = a - (a - b)⁺`: with `a = 1 + 4 α - 2 y` and
`b = y + (1 + α - 3 y)⁺`, the positive part `(a - b)⁺` is exactly `d_rk(y)` on `(1/3, 1/2)`,
and both vanish at `y = 1/2`. What remains is the affine identity
`7 - 7 y - 12 α + 1 + 4 α - 2 y = 8 - 9 y - 8 α`, the first branch of `R₀`.

## Main results

* `Zeta5Irr.outerExponent_eq_outerLimitingFunction_sub_rankDefect`: the identity above.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.4 (The outer asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

/-- On the near range `1/3 < y ≤ 1/2`,
`7 (1 - y) - 12 α - 5 min(α, 1 - 2 y) - 5 (1 + α - 3 y)⁺
  + min(1 + 4 α - 2 y, y + (1 + α - 3 y)⁺) = R₀(y) - d_rk(y)`. -/
@[zeta5irr "lem_norm_gout_near"]
theorem outerExponent_eq_outerLimitingFunction_sub_rankDefect {y : ℝ} (hy₁ : 1 / 3 < y)
    (hy₂ : y ≤ 1 / 2) :
    7 * (1 - y) - 12 * (innerRatio : ℝ) - 5 * min (innerRatio : ℝ) (1 - 2 * y) -
        5 * (1 + (innerRatio : ℝ) - 3 * y)⁺ +
        min (1 + 4 * (innerRatio : ℝ) - 2 * y) (y + (1 + (innerRatio : ℝ) - 3 * y)⁺) =
      outerLimitingFunction y - rankDefect y := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hmin : ∀ a b : ℝ, min a b = a - (a - b)⁺ := fun a b => by
    rcases le_total a b with h | h
    · rw [min_eq_left h, posPart_eq_zero.2 (by linarith), sub_zero]
    · rw [min_eq_right h, posPart_eq_self.2 (by linarith)]; ring
  have hd : rankDefect y =
      (1 + 4 * (innerRatio : ℝ) - 2 * y - (y + (1 + (innerRatio : ℝ) - 3 * y)⁺))⁺ := by
    rcases hy₂.lt_or_eq with hy₂ | rfl
    · rw [rankDefect_of_mem hy₁ hy₂]; ring_nf
    · rw [rankDefect_of_one_half_le le_rfl, hα,
        posPart_eq_zero.2 (show (1 + 3 / 40 - 3 * (1 / 2) : ℝ) ≤ 0 by norm_num)]
      exact (posPart_eq_zero.2 (by norm_num)).symm
  rw [outerLimitingFunction_of_le_half hy₂, hd, hmin (1 + 4 * (innerRatio : ℝ) - 2 * y)]
  ring

end Zeta5Irr
