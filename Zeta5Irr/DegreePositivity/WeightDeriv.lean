/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.ExpDerivForm
public import Zeta5Irr.DegreePositivity.WeightClosed

/-!
# The weight as a fourth derivative

For `y > 0` the weight is, up to the factor `y⁵ / 12`, the fourth derivative of
`1 / (e^{2πy} - 1)`:
`w(y) = y⁵ / 12 · (d/dy)⁴ 1 / (e^{2πy} - 1)`.
With `q = e^{-2πy}`, the fourth derivative equals
`(2π)⁴ q (1 + 11 q + 11 q² + q³) / (1 - q)⁵`, which is the closed form of the weight
divided by `y⁵ / 12`.

## Main results

* `Zeta5Irr.weight_eq_iteratedDeriv`: `w(y) = y⁵ / 12 · (d/dy)⁴ 1 / (e^{2πy} - 1)` for `y > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- **The weight as a fourth derivative.** For `y > 0`,
`w(y) = y⁵ / 12 · (d/dy)⁴ 1 / (e^{2πy} - 1)`. -/
@[zeta5irr "lem_w_deriv"]
theorem weight_eq_iteratedDeriv {y : ℝ} (hy : 0 < y) :
    weight y = y ^ 5 / 12 * iteratedDeriv 4 (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y := by
  rw [iteratedDeriv_one_div_exp_sub_one 4 hy.ne', aeval_derivNumerator_four,
    weight_eq_closed hy]
  have h2 : rexp (-2 * π * y) = rexp (-(2 * π * y)) := by ring_nf
  have h4 : rexp (-(4 * π * y)) = rexp (-(2 * π * y)) ^ 2 := by
    rw [← exp_nat_mul]; ring_nf
  have h6 : rexp (-(6 * π * y)) = rexp (-(2 * π * y)) ^ 3 := by
    rw [← exp_nat_mul]; ring_nf
  rw [h2, h4, h6]
  ring

end Zeta5Irr
