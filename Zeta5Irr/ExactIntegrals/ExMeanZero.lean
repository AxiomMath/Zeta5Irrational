/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExFracpart
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

/-!
# `Ψ_u` has mean zero on `[0, 1/2]`

For every real `u`, the function `Ψ_u(z) = ℓ(u, z) - 2u` integrates to zero over `[0, 1/2]`:
`∫₀^{1/2} Ψ_u(z) dz = 0`.

Writing `f` for the fractional part of `u` and `c = d₀(f) ∈ [0, 1/2]`, away from the null set
`{c, 1/2}` the integrand on `(0, 1/2]` equals `e(f) (𝟙_{z < c} - 2c)`, and both
`∫₀^{1/2} 𝟙_{z < c} dz` and `∫₀^{1/2} 2c dz` equal `c`.

## Main results

* `Zeta5Irr.integral_psi_eq_zero`: `∫₀^{1/2} Ψ_u(z) dz = 0`.

## Implementation notes

The indicator `𝟙_{z < c}` is written as `Set.indicator (Set.Iio c) 1`, so that its integral
over `(0, 1/2]` is the Lebesgue measure of `(0, 1/2] ∩ (-∞, c) = (0, c)`, instead of splitting
the interval at `c`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1 (fractional parts and the two `z`-integrals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- **Lemma (mean zero).** For every real `u`, `∫₀^{1/2} Ψ_u(z) dz = 0`. -/
@[zeta5irr "lem_ex_mean_zero"]
theorem integral_psi_eq_zero (u : ℝ) : ∫ z in (0 : ℝ)..1 / 2, psi u z = 0 := by
  set c := d₀ (Int.fract u)
  have hc₀ : 0 ≤ c := d₀_fract_nonneg u
  have hc₁ : c ≤ 1 / 2 := d₀_le_half _
  have hae : ∫ z in (0 : ℝ)..1 / 2, psi u z =
      ∫ z in (0 : ℝ)..1 / 2, esign (Int.fract u) *
        ((Set.Iio c).indicator (fun _ => (1 : ℝ)) z - 2 * c) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : volume ({c, 1 / 2} : Set ℝ) = 0 :=
      (Set.toFinite _).countable.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    rw [Set.uIoc_of_le (by norm_num)] at hzI
    rw [psi_eq_esign_mul u z hzI.1 (lt_of_le_of_ne hzI.2 hz.2) hz.1, Set.indicator_apply]
    rfl
  have hI : Set.Iio c ∩ Set.Ioc 0 (1 / 2) = Set.Ioo 0 c := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    exact ⟨fun ⟨h₁, h₂, _⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁, by linarith⟩⟩
  rw [hae, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
    intervalIntegral.integral_of_le (by norm_num), integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, hI, setIntegral_const]
  · simp [Real.volume_real_Ioo_of_le hc₀]
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact (integrableOn_const (by simp)).indicator measurableSet_Iio
  · exact intervalIntegrable_const

end Zeta5Irr
