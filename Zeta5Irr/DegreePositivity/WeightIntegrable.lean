/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.WeightPos
public import Zeta5Irr.DegreePositivity.WeightBound
public import Zeta5Irr.RealDeterminant.RealGamma652

/-!
# Polynomial moments of the weight are integrable

For every natural number `m`, the function `y ↦ yᵐ w(y)` is absolutely integrable on `(0, ∞)`.

On `(0, ∞)` the weight agrees with its closed form, a quotient of continuous functions whose
denominator `(1 - e^{-2πy})⁵` does not vanish, so `y ↦ yᵐ w(y)` is continuous there, hence
measurable. For `y > 0` we have `0 < yᵐ w(y) ≤ 8192 yᵐ (1 + y)⁵ e^{-2πy}`, and
`(1 + y)⁵ ≤ 32 (1 + y⁵)`, so the function is dominated by a constant multiple of
`yᵐ e^{-2πy} + y^{m+5} e^{-2πy}`, which is integrable on `(0, ∞)` (a Gamma-type integral).

## Main results

* `Zeta5Irr.continuousOn_weight`: the weight is continuous on `(0, ∞)`.
* `Zeta5Irr.integrableOn_pow_mul_weight`: `y ↦ yᵐ w(y)` is integrable on `(0, ∞)`.

## Implementation notes

The source expands `(1 + y)⁵` binomially; we use instead the cruder bound
`(1 + y)⁵ ≤ 32 (1 + y⁵)` for `y ≥ 0`, which needs only two exponential moments.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Real

namespace Zeta5Irr

/-- The weight is continuous on `(0, ∞)`. -/
theorem continuousOn_weight : ContinuousOn weight (Set.Ioi 0) := by
  have h : ContinuousOn (fun y : ℝ => (2 * π) ^ 4 * y ^ 5 / 12 *
      (rexp (-(2 * π * y)) * (1 + 11 * rexp (-(2 * π * y)) + 11 * rexp (-(4 * π * y)) +
        rexp (-(6 * π * y))) / (1 - rexp (-(2 * π * y))) ^ 5)) (Set.Ioi 0) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro y (hy : 0 < y)
    have : rexp (-(2 * π * y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [pi_pos])
    exact pow_ne_zero _ (by linarith)
  exact h.congr fun y hy => weight_eq_closed hy

/-- **Polynomial moments of the weight are integrable.** For every `m : ℕ`, the function
`y ↦ yᵐ w(y)` is integrable on `(0, ∞)`. -/
@[zeta5irr "lem_w_int_poly"]
theorem integrableOn_pow_mul_weight (m : ℕ) :
    IntegrableOn (fun y => y ^ m * weight y) (Set.Ioi 0) := by
  have hb : 0 < 2 * π := by positivity
  have hg : IntegrableOn (fun y : ℝ => 8192 * 32 *
      (y ^ m * rexp (-(2 * π * y)) + y ^ (m + 5) * rexp (-(2 * π * y)))) (Set.Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul m hb).add
      (integrableOn_pow_mul_exp_neg_mul (m + 5) hb)).const_mul _
  refine hg.mono' (((continuousOn_pow m).mul continuousOn_weight).aestronglyMeasurable
    measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y (hy : 0 < y) => ?_))
  have hw := weight_pos hy
  have hwle := weight_le hy
  have h5 := one_add_pow_le_two_pow_mul_one_add_pow 5 hy.le
  have hym : 0 ≤ y ^ m := pow_nonneg hy.le m
  have he : 0 < rexp (-(2 * π * y)) := exp_pos _
  rw [Real.norm_of_nonneg (by positivity)]
  calc y ^ m * weight y ≤ y ^ m * (8192 * (1 + y) ^ 5 * rexp (-(2 * π * y))) := by gcongr
    _ ≤ y ^ m * (8192 * (2 ^ 5 * (1 + y ^ 5)) * rexp (-(2 * π * y))) := by gcongr
    _ = _ := by ring

end Zeta5Irr
