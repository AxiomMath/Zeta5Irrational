/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.R0
public import Zeta5Irr.LimitingFunctions.Drank
public import Mathlib.Algebra.Order.Star.Real

/-!
# The integrand `Θ` of the outer integral

For `y ≥ 1/3` the integrand of the outer integral is
`Θ(y) = R₀(y) - d_rk(y) - 2 λ ⌊1/y⌋ + ∑_{j=1}^{5} (2 λ - j y)⁺`,
where `R₀` is the outer limiting function, `d_rk` the rank-defect correction,
`λ = 37/40` the order ratio and `(·)⁺` the positive part.

## Main definitions

* `Zeta5Irr.outerIntegrand`: the function `Θ`.

## Main results

* `Zeta5Irr.outerIntegrand_of_one_lt`: for `y > 1`, `Θ(y) = ∑_{j=1}^{5} (2 λ - j y)⁺`.
* `Zeta5Irr.outerIntegrand_of_two_mul_orderRatio_le`: `Θ(y) = 0` for `y ≥ 2 λ = 37/20`.

## Implementation notes

* The source defines `Θ` only for `y ≥ 1/3`. The formula makes sense for every real `y`
  (with `⌊1/y⌋ = 0` at `y = 0`), so `Θ` is defined on all of `ℝ`; the restriction
  `y ≥ 1/3` is carried by the lemmas that use it.
* The positive part is Mathlib's `PosPart.posPart`, and the floor is `Int.floor`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.4 (The outer integral).
-/

@[expose] public section

namespace Zeta5Irr

/-- The integrand of the outer integral,
`Θ(y) = R₀(y) - d_rk(y) - 2 λ ⌊1/y⌋ + ∑_{j=1}^{5} (2 λ - j y)⁺`, with `λ = 37/40` the order
ratio. The source restricts to `y ≥ 1/3`; the formula is used for all real `y`. -/
@[zeta5irr "def_ex_outer_integrand"]
noncomputable def outerIntegrand (y : ℝ) : ℝ :=
  outerLimitingFunction y - rankDefect y - 2 * (orderRatio : ℝ) * ⌊y⁻¹⌋ +
    ∑ j ∈ Finset.Icc 1 5, (2 * (orderRatio : ℝ) - (j : ℕ) * y)⁺

/-- For `y > 1`, only the positive-part sum survives: `Θ(y) = ∑_{j=1}^{5} (2 λ - j y)⁺`. -/
theorem outerIntegrand_of_one_lt {y : ℝ} (hy : 1 < y) :
    outerIntegrand y = ∑ j ∈ Finset.Icc 1 5, (2 * (orderRatio : ℝ) - (j : ℕ) * y)⁺ := by
  have hfl : ⌊y⁻¹⌋ = 0 := Int.floor_eq_zero_iff.2
    ⟨inv_nonneg.2 (by linarith), inv_lt_one_of_one_lt₀ hy⟩
  rw [outerIntegrand, outerLimitingFunction_of_one_lt hy,
    rankDefect_of_one_half_le (by linarith), hfl]
  simp

/-- `Θ(y) = 0` for `y ≥ 2 λ = 37/20`. -/
theorem outerIntegrand_of_two_mul_orderRatio_le {y : ℝ} (hy : 2 * (orderRatio : ℝ) ≤ y) :
    outerIntegrand y = 0 := by
  have hlam : (orderRatio : ℝ) = 37 / 40 := by norm_num [orderRatio]
  rw [outerIntegrand_of_one_lt (by linarith)]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  rw [posPart_eq_zero]
  nlinarith

end Zeta5Irr
