/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.WeightClosed

/-!
# Positivity of the weight

The weight `w(y)` is positive for every `y > 0`. With `q = e^{-2πy} ∈ (0, 1)`, the closed form
`w(y) = (2π)⁴ y⁵ / 12 · q (1 + 11 q + 11 q² + q³) / (1 - q)⁵` is a product and quotient of
positive factors.

## Main results

* `Zeta5Irr.weight_pos`: `0 < w(y)` for `y > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The weight is positive on the positive half-line: `0 < w(y)` for `y > 0`. -/
@[zeta5irr "lem_w_pos"]
theorem weight_pos {y : ℝ} (hy : 0 < y) : 0 < weight y := by
  rw [weight_eq_closed hy]
  have hq1 : rexp (-(2 * π * y)) < 1 :=
    Real.exp_lt_one_iff.2 (by have := pi_pos; nlinarith)
  have h1 : 0 < 1 - rexp (-(2 * π * y)) := sub_pos.2 hq1
  have := pi_pos
  positivity

end Zeta5Irr
