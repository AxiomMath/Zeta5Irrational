/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormGamhat
public import Zeta5Irr.PrimeSum.NormEllStep
public import Zeta5Irr.PrimeSum.NormUppersetMeasure
public import Mathlib.Tactic.ENatToNat

/-!
# Continuity of `Γ̂(x, σ)` in `σ`

For fixed `x`, the two-variable inner functional
`Γ̂(x, σ) = ∫₀^{1/2} (⌊2σ⌋ - b) (⌊2σ⌋ + b - ℓ - 5) dz + ({2σ}/2) (2⌊2σ⌋ - q̃(x) - 5)`
`  + ({2σ}/2 - ñ(x))₊`
is a continuous function of `σ`. The integrand is a quadratic polynomial in `m = ⌊2σ⌋`, so the
`z`-integral equals `F(m) = m²/2 - m (∫₀^{1/2} ℓ dz + 5/2) + C(x)`, and
`∫₀^{1/2} ℓ(x, z) dz = q̃(x)/2 + ñ(x)` by the step structure of `ℓ` and the measure of the
step set `S(x)`. Writing `2σ = m + f` with `f = {2σ}`, this gives
`Γ̂(x, σ) = F(2σ) + h({2σ})` with `h(f) = f ñ(x) - f²/2 + (f/2 - ñ(x))₊`. Since
`0 ≤ ñ(x) < 1/2`, `h(0) = h(1) = 0`, so `h ∘ fract` is continuous, and so is `Γ̂(x, ·)`.

## Main results

* `Zeta5Irr.integral_ell_right`: `∫₀^{1/2} ℓ(x, z) dz = q̃(x)/2 + ñ(x)`.
* `Zeta5Irr.innerLimitingGammaHat_eq_add_fract`: `Γ̂(x, σ) = F(2σ) + h({2σ})`.
* `Zeta5Irr.continuous_innerLimitingGammaHat`: `σ ↦ Γ̂(x, σ)` is continuous.

## Implementation notes

* The source states continuity on `(0, ∞)` for `x ≥ 3`, and proves it by checking the jumps at
  the half-integers `σ = (k + 1)/2`. The formula `Γ̂(x, σ) = F(2σ) + h({2σ})` removes the case
  analysis, and shows continuity on all of `ℝ` for every real `x`, which is the form proved here.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- The mean of the pole count: `∫₀^{1/2} ℓ(x, z) dz = q̃(x)/2 + ñ(x)`. -/
theorem integral_ell_right (x : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), (ell x z : ℝ) = basePoleCount x / 2 + baseHalfFract x := by
  have hS : MeasurableSet (normUpperSet x) := by
    unfold normUpperSet; split_ifs <;> measurability
  have hsub : normUpperSet x ⊆ Set.Ioc 0 (1 / 2) := by
    intro t ht
    rcases mem_normUpperSet.1 ht with ⟨h, h0, h1⟩ | ⟨h, h0, h1⟩
    · exact ⟨h0, by linarith⟩
    · exact ⟨by linarith [Int.fract_lt_one x], h1.le⟩
  have hae : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Set.uIoc 0 (1 / 2 : ℝ) →
      (ell x z : ℝ) = (⌊2 * x⌋ : ℝ) + (normUpperSet x).indicator 1 z := by
    have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 1 / 2 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with z hz hmem
    rw [Set.uIoc_of_le (by norm_num)] at hmem
    rw [ell_eq_floor_two_mul_add_indicator x hmem.1 (lt_of_le_of_ne hmem.2 hz)]
    push_cast
    congr 1
    by_cases h : z ∈ normUpperSet x <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_of_le (by norm_num),
    integral_indicator_one hS, measureReal_restrict_apply hS, Set.inter_eq_left.2 hsub,
    volume_real_normUpperSet, basePoleCount_def, baseHalfFract_eq_fract]
  · simp; ring
  · refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
      (measurable_const.indicator hS).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    refine (norm_indicator_le_norm_self _ _).trans ?_
    simp

/-- `Γ̂(x, σ) = F(2σ) + h({2σ})`, where `F(t) = t²/2 - t (q̃(x)/2 + ñ(x) + 5/2) + C(x)` with
`C(x) = ∫₀^{1/2} (-b) (b - ℓ - 5) dz`, and `h(f) = f ñ(x) - f²/2 + (f/2 - ñ(x))₊`. -/
theorem innerLimitingGammaHat_eq_add_fract (x σ : ℝ) :
    innerLimitingGammaHat x σ =
      ((2 * σ) ^ 2 / 2 - 2 * σ * (basePoleCount x / 2 + baseHalfFract x + 5 / 2) +
          ∫ z in (0 : ℝ)..(1 / 2), -weightedPoleCount x z *
            (weightedPoleCount x z - ell x z - 5)) +
        (Int.fract (2 * σ) * baseHalfFract x - Int.fract (2 * σ) ^ 2 / 2 +
          (Int.fract (2 * σ) / 2 - baseHalfFract x)⁺) := by
  rw [innerLimitingGammaHat]
  set k : ℝ := ((⌊2 * σ⌋ : ℤ) : ℝ)
  set f := Int.fract (2 * σ)
  have ht : 2 * σ = k + f := (Int.floor_add_fract _).symm
  have hint : (∫ z in (0 : ℝ)..(1 / 2), (k - weightedPoleCount x z) *
      (k + weightedPoleCount x z - ell x z - 5)) =
      (∫ z in (0 : ℝ)..(1 / 2), -weightedPoleCount x z *
        (weightedPoleCount x z - ell x z - 5)) +
      (k ^ 2 / 2 - k * ((∫ z in (0 : ℝ)..(1 / 2), (ell x z : ℝ)) + 5 / 2)) := by
    have hfun : (fun z => (k - weightedPoleCount x z) *
        (k + weightedPoleCount x z - ell x z - 5)) = fun z => -weightedPoleCount x z *
        (weightedPoleCount x z - ell x z - 5) + (k ^ 2 - 5 * k - k * (ell x z : ℝ)) := by
      funext z; ring
    have h0 : IntervalIntegrable (fun z => -weightedPoleCount x z *
        (weightedPoleCount x z - ell x z - 5)) volume 0 (1 / 2) := by
      simpa using intervalIntegrable_innerIntegrand x 0 0 (1 / 2)
    rw [hfun, intervalIntegral.integral_add h0
      ((intervalIntegrable_const).sub ((intervalIntegrable_ell_right x 0 _).const_mul k)),
      intervalIntegral.integral_sub intervalIntegrable_const
        ((intervalIntegrable_ell_right x 0 _).const_mul k),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp; ring
  rw [hint, integral_ell_right]
  linear_combination
    (-(k + f + 2 * σ) / 2 + (basePoleCount x / 2 + baseHalfFract x + 5 / 2)) * ht

/-- For every `x`, `σ ↦ Γ̂(x, σ)` is continuous (the source states it on `(0, ∞)` for `x ≥ 3`). -/
@[zeta5irr "lem_norm_Gamhat_shift"]
theorem continuous_innerLimitingGammaHat (x : ℝ) : Continuous (innerLimitingGammaHat x) := by
  set n := baseHalfFract x
  have hn0 : 0 ≤ n := baseHalfFract_nonneg x
  have hn1 : n < 1 / 2 := baseHalfFract_lt_half x
  set h : ℝ → ℝ := fun f => f * n - f ^ 2 / 2 + (f / 2 - n)⁺
  have hh : Continuous ((h ∘ Int.fract) ∘ fun σ : ℝ => 2 * σ) := by
    refine ((ContinuousOn.comp_fract'' ?_ ?_)).comp (continuous_const.mul continuous_id)
    · exact Continuous.continuousOn (by fun_prop)
    · simp only [h, posPart_eq_zero.2 (by linarith : (0 : ℝ) / 2 - n ≤ 0),
        posPart_eq_self.2 (by linarith : (0 : ℝ) ≤ 1 / 2 - n)]
      ring
  have heq : innerLimitingGammaHat x = fun σ =>
      ((2 * σ) ^ 2 / 2 - 2 * σ * (basePoleCount x / 2 + n + 5 / 2) +
          ∫ z in (0 : ℝ)..(1 / 2), -weightedPoleCount x z *
            (weightedPoleCount x z - ell x z - 5)) +
        ((h ∘ Int.fract) ∘ fun σ : ℝ => 2 * σ) σ := by
    funext σ
    exact innerLimitingGammaHat_eq_add_fract x σ
  rw [heq]
  exact Continuous.add (by fun_prop) hh

end Zeta5Irr
