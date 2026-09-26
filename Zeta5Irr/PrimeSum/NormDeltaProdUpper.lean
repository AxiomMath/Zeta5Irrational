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
# An upper bound for the integral of a product of two deviations

For all real `x₁, x₂`, the deviations `δ(xᵢ, z)` of `Zeta5Irr.ellDeviation` satisfy
`∫_0^{1/2} δ(x₁, z) δ(x₂, z) dz ≤ 1/8`.

Write `nᵢ = {2xᵢ}/2 = |S(xᵢ)|`, so `0 ≤ nᵢ < 1/2`. Since `S(x₁) ∩ S(x₂) ⊆ S(xᵢ)`, the
measure of the intersection is at most `min(n₁, n₂)`, so the integral is at most
`min(n₁, n₂) - 2 n₁ n₂`. If `n₁ ≤ n₂` this is `n₁ (1 - 2n₂) ≤ n₁ (1 - 2n₁)
= 1/8 - 2 (n₁ - 1/4)² ≤ 1/8`, and symmetrically otherwise.

## Main results

* `Zeta5Irr.integral_ellDeviation_mul_ellDeviation_le`: the bound above.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2 (The step structure of the pole counts).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- `∫_0^{1/2} δ(x₁, z) δ(x₂, z) dz ≤ 1/8`. -/
@[zeta5irr "lem_norm_delta_prod_upper"]
theorem integral_ellDeviation_mul_ellDeviation_le (x₁ x₂ : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), ellDeviation x₁ z * ellDeviation x₂ z ≤ 1 / 8 := by
  have hfin : ∀ x, volume (normUpperSet x) ≠ ⊤ := fun x => by
    rw [volume_normUpperSet_eq]; exact ENNReal.ofReal_ne_top
  have h₁ : volume.real (normUpperSet x₁ ∩ normUpperSet x₂) ≤ Int.fract (2 * x₁) / 2 := by
    rw [← volume_real_normUpperSet]
    exact measureReal_mono Set.inter_subset_left (hfin x₁)
  have h₂ : volume.real (normUpperSet x₁ ∩ normUpperSet x₂) ≤ Int.fract (2 * x₂) / 2 := by
    rw [← volume_real_normUpperSet]
    exact measureReal_mono Set.inter_subset_right (hfin x₂)
  rw [integral_ellDeviation_mul_ellDeviation]
  have ha₀ := Int.fract_nonneg (2 * x₁)
  have ha₁ := Int.fract_lt_one (2 * x₁)
  have hb₀ := Int.fract_nonneg (2 * x₂)
  have hb₁ := Int.fract_lt_one (2 * x₂)
  rcases le_total (Int.fract (2 * x₁)) (Int.fract (2 * x₂)) with h | h
  · nlinarith [sq_nonneg (Int.fract (2 * x₁) - 1 / 2)]
  · nlinarith [sq_nonneg (Int.fract (2 * x₂) - 1 / 2)]

end Zeta5Irr
