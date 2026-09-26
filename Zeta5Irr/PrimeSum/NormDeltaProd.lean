/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormDeltaFormula
public import Zeta5Irr.PrimeSum.NormUppersetMeasure
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat

/-!
# The integral of a product of two deviations

For real `x₁, x₂`, the deviations `δ(xᵢ, z)` of `Zeta5Irr.ellDeviation` satisfy
`∫_0^{1/2} δ(x₁, z) δ(x₂, z) dz = |S(x₁) ∩ S(x₂)| - {2x₁}{2x₂}/2`, where `S(x)` is the step
set `Zeta5Irr.normUpperSet` and `|·|` is Lebesgue measure. On `(0, 1/2)` the integrand is
`(𝟙_{S(x₁)} - {2x₁})(𝟙_{S(x₂)} - {2x₂})`; expanding, and using `S(xᵢ) ⊆ (0, 1/2)` and
`|S(xᵢ)| = {2xᵢ}/2`, gives the formula.

## Main results

* `Zeta5Irr.integral_ellDeviation_mul_ellDeviation`: the formula above.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2 (The step structure of the pole counts).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- `∫_0^{1/2} δ(x₁, z) δ(x₂, z) dz = |S(x₁) ∩ S(x₂)| - {2x₁}{2x₂}/2`. -/
@[zeta5irr "lem_norm_delta_prod"]
theorem integral_ellDeviation_mul_ellDeviation (x₁ x₂ : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), ellDeviation x₁ z * ellDeviation x₂ z =
      volume.real (normUpperSet x₁ ∩ normUpperSet x₂) -
        Int.fract (2 * x₁) * Int.fract (2 * x₂) / 2 := by
  set a := Int.fract (2 * x₁)
  set b := Int.fract (2 * x₂)
  set S₁ := normUpperSet x₁
  set S₂ := normUpperSet x₂
  have hS₁ : MeasurableSet S₁ := measurableSet_normUpperSet x₁
  have hS₂ : MeasurableSet S₂ := measurableSet_normUpperSet x₂
  have hsub₁ : S₁ ⊆ Set.Ioo 0 (1 / 2) := normUpperSet_subset_Ioo x₁
  have hsub₂ : S₂ ⊆ Set.Ioo 0 (1 / 2) := normUpperSet_subset_Ioo x₂
  -- the integral of an indicator of a subset of `(0, 1/2)`
  have hind : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo 0 (1 / 2) →
      ∫ z in Set.Ioo (0 : ℝ) (1 / 2), s.indicator (1 : ℝ → ℝ) z = volume.real s := by
    intro s hs hsub
    rw [integral_indicator_one hs, measureReal_restrict_apply hs, Set.inter_eq_left.2 hsub]
  have hint : ∀ s : Set ℝ, MeasurableSet s →
      IntegrableOn (s.indicator (1 : ℝ → ℝ)) (Set.Ioo 0 (1 / 2)) :=
    fun s hs => (integrableOn_const (by simp)).indicator hs
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hcongr : Set.EqOn (fun z => ellDeviation x₁ z * ellDeviation x₂ z)
      (fun z => (S₁ ∩ S₂).indicator 1 z - b * S₁.indicator 1 z - a * S₂.indicator 1 z + a * b)
      (Set.Ioo 0 (1 / 2)) := by
    intro z hz
    simp only
    rw [ellDeviation_eq_indicator_sub_fract x₁ hz.1 hz.2,
      ellDeviation_eq_indicator_sub_fract x₂ hz.1 hz.2, Set.inter_indicator_one]
    simp only [Pi.mul_apply]
    ring
  have i₀ : IntegrableOn (fun z => (S₁ ∩ S₂).indicator (1 : ℝ → ℝ) z) (Set.Ioo 0 (1 / 2)) :=
    hint _ (hS₁.inter hS₂)
  have i₁ : IntegrableOn (fun z => b * S₁.indicator (1 : ℝ → ℝ) z) (Set.Ioo 0 (1 / 2)) :=
    (hint _ hS₁).const_mul b
  have i₂ : IntegrableOn (fun z => a * S₂.indicator (1 : ℝ → ℝ) z) (Set.Ioo 0 (1 / 2)) :=
    (hint _ hS₂).const_mul a
  have i₀₁ : IntegrableOn (fun z => (S₁ ∩ S₂).indicator (1 : ℝ → ℝ) z -
      b * S₁.indicator (1 : ℝ → ℝ) z) (Set.Ioo 0 (1 / 2)) := i₀.sub i₁
  have i₀₁₂ : IntegrableOn (fun z => (S₁ ∩ S₂).indicator (1 : ℝ → ℝ) z -
      b * S₁.indicator (1 : ℝ → ℝ) z - a * S₂.indicator (1 : ℝ → ℝ) z) (Set.Ioo 0 (1 / 2)) :=
    i₀₁.sub i₂
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
    integral_add i₀₁₂ (integrableOn_const (by simp)),
    integral_sub i₀₁ i₂, integral_sub i₀ i₁,
    integral_const_mul, integral_const_mul, hind _ (hS₁.inter hS₂)
      (Set.inter_subset_left.trans hsub₁), hind _ hS₁ hsub₁, hind _ hS₂ hsub₂,
    setIntegral_const, volume_real_normUpperSet, volume_real_normUpperSet, Real.volume_real_Ioo]
  simp only [smul_eq_mul]
  norm_num
  ring

end Zeta5Irr
