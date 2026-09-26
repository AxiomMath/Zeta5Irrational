/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.WeightSeries
public import Mathlib.Algebra.Order.Star.Real

/-!
# The weight in closed form

For `y > 0`, putting `q = e^{-2πy} ∈ (0, 1)` in the generating function
`∑_{ℓ ≥ 1} ℓ⁴ q^ℓ = q (1 + 11 q + 11 q² + q³) / (1 - q)⁵` turns the series defining the
weight into the closed form
`w(y) = (2π)⁴ y⁵ / 12 · e^{-2πy} (1 + 11 e^{-2πy} + 11 e^{-4πy} + e^{-6πy}) / (1 - e^{-2πy})⁵`.

## Main results

* `Zeta5Irr.weight_eq_closed`: the closed form of `w(y)` for `y > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The closed form of the weight: for `y > 0`,
`w(y) = (2π)⁴ y⁵ / 12 · e^{-2πy} (1 + 11 e^{-2πy} + 11 e^{-4πy} + e^{-6πy}) / (1 - e^{-2πy})⁵`. -/
@[zeta5irr "lem_w_closed"]
theorem weight_eq_closed {y : ℝ} (hy : 0 < y) :
    weight y = (2 * π) ^ 4 * y ^ 5 / 12 *
      (rexp (-(2 * π * y)) * (1 + 11 * rexp (-(2 * π * y)) + 11 * rexp (-(4 * π * y)) +
        rexp (-(6 * π * y))) / (1 - rexp (-(2 * π * y))) ^ 5) := by
  set q := rexp (-(2 * π * y)) with hq
  have hq0 : 0 < q := exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by have := pi_pos; nlinarith)
  have hpow (n : ℕ) : rexp (-(2 * π * n * y)) = q ^ n := by
    rw [hq, ← exp_nat_mul]; ring_nf
  have h4 : rexp (-(4 * π * y)) = q ^ 2 := by rw [← hpow]; push_cast; ring_nf
  have h6 : rexp (-(6 * π * y)) = q ^ 3 := by rw [← hpow]; push_cast; ring_nf
  rw [weight, h4, h6]
  simp_rw [hpow]
  rw [tsum_natCast_pow_four_mul_pow (by rw [abs_of_pos hq0]; exact hq1)]

end Zeta5Irr
