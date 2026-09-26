/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormDeltaProd
public import Mathlib.Algebra.Order.Star.Real

/-!
# A lower bound for the integral of a product of two deviations

For all real `x₁, x₂`, the deviations `δ(xᵢ, z)` of `Zeta5Irr.ellDeviation` satisfy
`∫_0^{1/2} δ(x₁, z) δ(x₂, z) dz ≥ -1/8`.

Write `nᵢ = {2xᵢ}/2 ∈ [0, 1/2)`, the measure of the step set `S(xᵢ)`. Both step sets lie in
`(0, 1/2)`, so `|S(x₁) ∩ S(x₂)| ≥ max(0, n₁ + n₂ - 1/2)`, and by the product formula
`Zeta5Irr.integral_ellDeviation_mul_ellDeviation` the integral is at least
`max(0, n₁ + n₂ - 1/2) - 2 n₁ n₂`. With `Σ = n₁ + n₂` and `2 n₁ n₂ ≤ Σ² / 2`, this is at least
`-Σ²/2 ≥ -1/8` when `Σ ≤ 1/2`, and at least `-(Σ - 1)²/2 ≥ -1/8` when `1/2 < Σ < 1`.

## Main results

* `Zeta5Irr.neg_one_div_eight_le_integral_ellDeviation_mul`: the lower bound `-1/8`.
* `Zeta5Irr.volume_real_normUpperSet_inter_ge`: `|S(x₁) ∩ S(x₂)| ≥ |S(x₁)| + |S(x₂)| - 1/2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2 (The step structure of the pole counts).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- Two step sets lying in `(0, 1/2)` overlap in measure at least `|S(x₁)| + |S(x₂)| - 1/2`. -/
theorem volume_real_normUpperSet_inter_ge (x₁ x₂ : ℝ) :
    volume.real (normUpperSet x₁) + volume.real (normUpperSet x₂) - 1 / 2 ≤
      volume.real (normUpperSet x₁ ∩ normUpperSet x₂) := by
  have hU := measureReal_union_add_inter (μ := volume) (s := normUpperSet x₁)
    (measurableSet_normUpperSet x₂)
    (measure_ne_top_of_subset (normUpperSet_subset_Ioo x₁) (by simp))
    (measure_ne_top_of_subset (normUpperSet_subset_Ioo x₂) (by simp))
  have hle : volume.real (normUpperSet x₁ ∪ normUpperSet x₂) ≤ 1 / 2 := by
    calc volume.real (normUpperSet x₁ ∪ normUpperSet x₂)
        ≤ volume.real (Set.Ioo (0 : ℝ) (1 / 2)) :=
          measureReal_mono (Set.union_subset (normUpperSet_subset_Ioo x₁)
            (normUpperSet_subset_Ioo x₂)) (by simp)
      _ = 1 / 2 := by simp
  linarith

/-- `∫_0^{1/2} δ(x₁, z) δ(x₂, z) dz ≥ -1/8`. -/
@[zeta5irr "lem_norm_delta_prod_lower"]
theorem neg_one_div_eight_le_integral_ellDeviation_mul (x₁ x₂ : ℝ) :
    -(1 / 8 : ℝ) ≤ ∫ z in (0 : ℝ)..(1 / 2), ellDeviation x₁ z * ellDeviation x₂ z := by
  rw [integral_ellDeviation_mul_ellDeviation]
  have hI := volume_real_normUpperSet_inter_ge x₁ x₂
  have h0 : 0 ≤ volume.real (normUpperSet x₁ ∩ normUpperSet x₂) := measureReal_nonneg
  rw [volume_real_normUpperSet, volume_real_normUpperSet] at hI
  have a0 := Int.fract_nonneg (2 * x₁)
  have a1 := Int.fract_lt_one (2 * x₁)
  have b0 := Int.fract_nonneg (2 * x₂)
  have b1 := Int.fract_lt_one (2 * x₂)
  set a := Int.fract (2 * x₁)
  set b := Int.fract (2 * x₂)
  rcases le_or_gt (a + b) 1 with h | h
  · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]

end Zeta5Irr
