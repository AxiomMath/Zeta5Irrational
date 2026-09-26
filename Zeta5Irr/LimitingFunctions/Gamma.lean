/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.BXz
public import Zeta5Irr.LimitingFunctions.Sx
public import Zeta5Irr.LimitingFunctions.Nplus
public import Zeta5Irr.ExactIntegrals.ExMeanZero

/-!
# The inner limiting function `Γ`

The inner limiting function is
`Γ(x) = ∫₀^{1/2} (T̃(x) - b(x, z)) (T̃(x) + b(x, z) - ℓ(x, z) - 5) dz`
`  + s̃(x) (2 T̃(x) - q̃(x) - 5) + (s̃(x) - ñ(x))₊`,
where `T̃(x) = ⌊2 H x⌋` is the base allocation, `s̃(x) = H x - T̃(x) / 2` the allocation
remainder, `q̃(x) = ⌊2 x⌋` the pole count at the base, `ñ(x) = (2 x - q̃(x)) / 2` the pole
count remainder, `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1` the pole count and `b(x, z) = 3 ℓ(α x, z)`
the weighted pole count. The integrand is, for each fixed `x`, a step function of `z` taking
finitely many values, so the integral is elementary. The name `Γ` has nothing to do with the
gamma function.

## Main definitions

* `Zeta5Irr.innerLimitingGamma`: the inner limiting function `Γ`.

## Main results

* `Zeta5Irr.innerLimitingGamma_def`: the defining formula of `Γ`.
* `Zeta5Irr.intervalIntegrable_innerIntegrand`: for each `x` and `m`, the integrand
  `z ↦ (m - b(x, z)) (m + b(x, z) - ℓ(x, z) - 5)` is interval integrable on every
  bounded interval; for `m = T̃(x)` this is the integrand of `Γ`, so the integral in `Γ` is a
  genuine Lebesgue integral and not the junk value `0`.
* `Zeta5Irr.integral_innerIntegrand_eq`: that integral with the terms linear in `Ψ`
  integrated out, leaving `∫ Ψ_{αx}²` and `∫ Ψ_x Ψ_{αx}`.

## Implementation notes

* The source defines `Γ` only for `x ≥ 3`. Every ingredient is defined on all of `ℝ` and the
  formula makes sense for every real `x`, so `Γ` is defined on all of `ℝ`; the restriction
  `x ≥ 3` is carried by the lemmas that use it.
* The positive part `(t)₊ = max(t, 0)` is Mathlib's `posPart`, written `t⁺`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1 (The inner limiting function), equation (5.4).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- The inner limiting function
`Γ(x) = ∫₀^{1/2} (T̃(x) - b(x, z)) (T̃(x) + b(x, z) - ℓ(x, z) - 5) dz`
`  + s̃(x) (2 T̃(x) - q̃(x) - 5) + (s̃(x) - ñ(x))₊`.
The source restricts to `x ≥ 3`; the formula is used for all real `x`. -/
@[zeta5irr "def_Gamma"]
noncomputable def innerLimitingGamma (x : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), (innerLimit x - weightedPoleCount x z) *
      (innerLimit x + weightedPoleCount x z - ell x z - 5)) +
    allocationRemainder x * (2 * innerLimit x - basePoleCount x - 5) +
    (allocationRemainder x - baseHalfFract x)⁺

/-- Unfolding lemma for `Γ`. -/
theorem innerLimitingGamma_def (x : ℝ) :
    innerLimitingGamma x =
      (∫ z in (0 : ℝ)..(1 / 2), (innerLimit x - weightedPoleCount x z) *
          (innerLimit x + weightedPoleCount x z - ell x z - 5)) +
        allocationRemainder x * (2 * innerLimit x - basePoleCount x - 5) +
        max (allocationRemainder x - baseHalfFract x) 0 :=
  rfl

/-- `z ↦ ℓ(x, z)` is measurable. -/
theorem measurable_ell_right (x : ℝ) : Measurable fun z => (ell x z : ℝ) := by
  simp only [ell_def]
  push_cast
  fun_prop

/-- For fixed `x`, `z ↦ ℓ(x, z)` is interval integrable on every interval. -/
theorem intervalIntegrable_ell_right (x a c : ℝ) :
    IntervalIntegrable (fun z => (ell x z : ℝ)) volume a c := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => 2 * |x| + 1) intervalIntegrable_const
    (measurable_ell_right x).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  dsimp only; rw [Real.norm_eq_abs]
  exact abs_ell_le x z

/-- For fixed `x` and `m`, the integrand `z ↦ (m - b(x, z)) (m + b(x, z) - ℓ(x, z) - 5)` of `Γ̂`
(for `m = T̃(x)`, of `Γ`) is interval integrable on every interval. -/
theorem intervalIntegrable_innerIntegrand (x m a c : ℝ) :
    IntervalIntegrable (fun z => (m - weightedPoleCount x z) *
      (m + weightedPoleCount x z - ell x z - 5)) volume a c := by
  set A := (innerRatio : ℝ) * x
  have hB : ∀ z, |weightedPoleCount x z| ≤ 3 * (2 * |A| + 1) := fun z => by
    rw [weightedPoleCount_def, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left (abs_ell_le A z) (by norm_num)
  have hmeas : Measurable fun z => (m - weightedPoleCount x z) *
      (m + weightedPoleCount x z - ell x z - 5) := by
    have := measurable_ell_right A
    have := measurable_ell_right x
    simp only [weightedPoleCount_def]
    fun_prop
  refine IntervalIntegrable.mono_fun' (g := fun _ => (|m| + 3 * (2 * |A| + 1)) *
      (|m| + 3 * (2 * |A| + 1) + (2 * |x| + 1) + 5)) intervalIntegrable_const
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  dsimp only; rw [Real.norm_eq_abs, abs_mul]
  have h1 : |m - weightedPoleCount x z| ≤ |m| + 3 * (2 * |A| + 1) :=
    (abs_sub _ _).trans (by linarith [hB z])
  have h2 : |m + weightedPoleCount x z - ell x z - 5| ≤
      |m| + 3 * (2 * |A| + 1) + (2 * |x| + 1) + 5 := by
    have := abs_sub (m + weightedPoleCount x z - ell x z) 5
    have := abs_sub (m + weightedPoleCount x z) (ell x z)
    have := abs_add_le m (weightedPoleCount x z)
    norm_num at *
    linarith [hB z, abs_ell_le x z]
  exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

/-- The integral in `Γ` (with `T̃(x)` replaced by any `m`), with the terms linear in `Ψ`
integrated out: `∫_0^{1/2} (m - b)(m + b - ℓ - 5) dz`
`  = a₀ c₀ / 2 - 9 ∫ Ψ_{αx}(z)² dz + 3 ∫ Ψ_x(z) Ψ_{αx}(z) dz`,
where `a₀ = m - 6αx` and `c₀ = m + 6αx - 2x - 5`. -/
theorem integral_innerIntegrand_eq (x m : ℝ) :
    (∫ z in (0 : ℝ)..(1 / 2), (m - weightedPoleCount x z) *
      (m + weightedPoleCount x z - ell x z - 5)) =
      (m - 6 * innerRatio * x) * (m + 6 * innerRatio * x - 2 * x - 5) / 2 -
        9 * (∫ z in (0 : ℝ)..(1 / 2), psi ((innerRatio : ℝ) * x) z ^ 2) +
        3 * ∫ z in (0 : ℝ)..(1 / 2), psi x z * psi ((innerRatio : ℝ) * x) z := by
  set a₀ := m - 6 * innerRatio * x
  set c₀ := m + 6 * innerRatio * x - 2 * x - 5
  set y := (innerRatio : ℝ) * x
  have hf : (fun z => (m - weightedPoleCount x z) *
      (m + weightedPoleCount x z - ell x z - 5)) = fun z =>
        a₀ * c₀ + 3 * (a₀ - c₀) * psi y z - a₀ * psi x z -
          9 * psi y z ^ 2 + 3 * (psi x z * psi y z) := by
    funext z
    simp only [weightedPoleCount_def, psi_def, a₀, c₀, y]
    ring
  have h₁ : IntervalIntegrable (fun z => 3 * (a₀ - c₀) * psi y z) volume 0 (1 / 2) :=
    (intervalIntegrable_psi y 0 _).const_mul _
  have h₂ : IntervalIntegrable (fun z => a₀ * psi x z) volume 0 (1 / 2) :=
    (intervalIntegrable_psi x 0 _).const_mul _
  have h₃ : IntervalIntegrable (fun z => 9 * psi y z ^ 2) volume 0 (1 / 2) := by
    simpa only [sq] using (intervalIntegrable_psi_mul_psi y y 0 (1 / 2)).const_mul 9
  have h₄ : IntervalIntegrable (fun z => 3 * (psi x z * psi y z)) volume 0 (1 / 2) :=
    (intervalIntegrable_psi_mul_psi x y 0 (1 / 2)).const_mul _
  have h₀ : IntervalIntegrable (fun _ : ℝ => a₀ * c₀) volume 0 (1 / 2) :=
    intervalIntegrable_const
  rw [hf, intervalIntegral.integral_add (((h₀.add h₁).sub h₂).sub h₃) h₄,
    intervalIntegral.integral_sub ((h₀.add h₁).sub h₂) h₃,
    intervalIntegral.integral_sub (h₀.add h₁) h₂, intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_psi_eq_zero, integral_psi_eq_zero, intervalIntegral.integral_const]
  simp only [smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

end Zeta5Irr
