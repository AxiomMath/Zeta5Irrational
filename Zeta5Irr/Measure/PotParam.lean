/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Arcsine

/-!
# The arcsine measure as the image of the uniform measure on the circle

For reals `a < b`, the arcsine measure `ω_{[a,b]}` is the image of the uniform probability
measure `dθ / 2π` on `[0, 2π)` under `θ ↦ (a + b)/2 + (b - a)/2 cos θ`.

Write `m = (a + b)/2` and `r = (b - a)/2 > 0`. On each of the half-circles `(0, π)` and
`(π, 2π)` the map `θ ↦ m + r cos θ` is an injective `C¹` map onto `(a, b)` with derivative
`-r sin θ`, and `(u - a)(b - u) = r² sin² θ` at `u = m + r cos θ`. The change of variables formula
therefore turns the arcsine mass `∫_{E ∩ (a, b)} du / (π √((u - a)(b - u)))` of a Borel set `E`
into `π⁻¹` times the Lebesgue measure of the set of `θ` in either half-circle with
`m + r cos θ ∈ E`. Averaging the two half-circles, which together make up `[0, 2π)` up to a null
set, gives the claim.

## Main results

* `Zeta5Irr.arcsineMeasure_eq_of_cos_param`: the change of variables on one half-circle.
* `Zeta5Irr.arcsineMeasure_eq_volume_Ioo_zero_pi`: the case of the half-circle `(0, π)`.
* `Zeta5Irr.map_cos_param_eq_arcsineMeasure`: `ω_{[a,b]}` is the image of `dθ / 2π` on
  `[0, 2π)` under `θ ↦ (a + b)/2 + (b - a)/2 cos θ`.
* `Zeta5Irr.integral_arcsineMeasure_eq`: the corresponding formula for integrals.

## Implementation notes

The blueprint compares the two measures on the intervals `(a, s]`, computing both masses as
`1 - arccos((s - m)/r) / π`. Here the measures are compared on every Borel set at once, by the
change of variables formula on each half-circle; this avoids the distribution functions and
uses `arccos` only to see that each half-circle maps onto `(a, b)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.2 (The arcsine measure and its potential).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real
open scoped ENNReal

/-- Off the zeros of `sin`, the point `(a + b)/2 + (b - a)/2 cos θ` lies in `(a, b)`. -/
lemma cos_param_mem_Ioo {a b θ : ℝ} (hab : a < b) (hθ : sin θ ≠ 0) :
    (a + b) / 2 + (b - a) / 2 * cos θ ∈ Ioo a b := by
  have h1 : cos θ ^ 2 < 1 := by
    have := sin_sq_add_cos_sq θ
    have := pow_pos (abs_pos.2 hθ) 2
    rw [sq_abs] at this
    linarith
  have h2 : |cos θ| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]; exact h1
  rw [abs_lt] at h2
  constructor <;> nlinarith

/-- Change of variables for the arcsine measure along `θ ↦ (a + b)/2 + (b - a)/2 cos θ`
on a piece `s` of the circle avoiding the zeros of `sin`, on which the map is injective with
image `(a, b)`. -/
lemma arcsineMeasure_eq_of_cos_param {a b : ℝ} (hab : a < b) {s : Set ℝ} (hs : MeasurableSet s)
    (hsin : ∀ θ ∈ s, sin θ ≠ 0)
    (hinj : InjOn (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) s)
    (himg : (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) '' s = Ioo a b)
    {E : Set ℝ} (hE : MeasurableSet E) :
    arcsineMeasure a b E =
      ENNReal.ofReal π⁻¹ *
        volume (s ∩ (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) ⁻¹' E) := by
  set f : ℝ → ℝ := fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ with hf
  have hfm : Measurable f := by fun_prop
  have hr : 0 < (b - a) / 2 := by linarith
  rw [arcsineMeasure, withDensity_apply _ hE, ← lintegral_indicator hE]
  have h1 : ∫⁻ u, E.indicator (arcsinePDF a b) u =
      ∫⁻ u in Ioo a b, E.indicator (arcsinePDF a b) u := by
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext u
    by_cases hu : u ∈ Ioo a b
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu]
      by_cases huE : u ∈ E
      · rw [indicator_of_mem huE, arcsinePDF_of_notMem hu]
      · rw [indicator_of_notMem huE]
  rw [h1, ← himg, lintegral_image_eq_lintegral_abs_deriv_mul hs
    (f' := fun θ ↦ -((b - a) / 2 * sin θ)) _ hinj]
  swap
  · intro θ _
    exact (((hasDerivAt_cos θ).const_mul ((b - a) / 2)).const_add ((a + b) / 2)).hasDerivWithinAt
      |>.congr_deriv (by ring)
  rw [inter_comm, ← Measure.restrict_apply (hfm hE), ← lintegral_indicator_one (hfm hE),
    ← lintegral_const_mul _ (measurable_one.indicator (hfm hE))]
  refine setLIntegral_congr_fun hs (fun θ hθ ↦ ?_)
  have hmem := cos_param_mem_Ioo hab (hsin θ hθ)
  by_cases hθE : f θ ∈ E
  · rw [indicator_of_mem hθE, indicator_of_mem (show θ ∈ f ⁻¹' E from hθE), Pi.one_apply,
      mul_one, arcsinePDF, arcsinePDFReal_of_mem hmem, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    have hprod : (f θ - a) * (b - f θ) = ((b - a) / 2 * sin θ) ^ 2 := by
      simp only [hf]
      have := sin_sq_add_cos_sq θ
      linear_combination (-(b - a) ^ 2 / 4) * this
    have hne : (b - a) / 2 * sin θ ≠ 0 := mul_ne_zero hr.ne' (hsin θ hθ)
    rw [hprod, sqrt_sq_eq_abs, abs_neg]
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ (abs_pos.2 hne).ne', mul_one]
  · rw [indicator_of_notMem hθE, indicator_of_notMem (show θ ∉ f ⁻¹' E from hθE), mul_zero,
      mul_zero]

/-- The map `θ ↦ (a + b)/2 + (b - a)/2 cos θ` sends a set `s` on which `sin` does not vanish onto
`(a, b)`, provided every `c ∈ (-1, 1)` is `cos θ` for some `θ ∈ s`. -/
lemma image_cos_param {a b : ℝ} (hab : a < b) {s : Set ℝ} (hsin : ∀ θ ∈ s, sin θ ≠ 0)
    (hsurj : ∀ c ∈ Ioo (-1 : ℝ) 1, ∃ θ ∈ s, cos θ = c) :
    (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) '' s = Ioo a b := by
  have hr : 0 < (b - a) / 2 := by linarith
  refine Subset.antisymm ?_ fun u hu ↦ ?_
  · rintro _ ⟨θ, hθ, rfl⟩
    exact cos_param_mem_Ioo hab (hsin θ hθ)
  · obtain ⟨θ, hθ, hc⟩ := hsurj ((u - (a + b) / 2) / ((b - a) / 2)) ⟨by
      rw [lt_div_iff₀ hr]; linarith [hu.1], by rw [div_lt_iff₀ hr]; linarith [hu.2]⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [hc]
    rw [mul_div_cancel₀ _ hr.ne']
    ring

/-- The map `θ ↦ (a + b)/2 + (b - a)/2 cos θ` is injective wherever `cos` is. -/
lemma injOn_cos_param {a b : ℝ} (hab : a < b) {s : Set ℝ} (hs : InjOn cos s) :
    InjOn (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) s := by
  intro x hx y hy hxy
  have hr : (b - a) / 2 ≠ 0 := by linarith
  exact hs hx hy (mul_left_cancel₀ hr (add_left_cancel hxy))

/-- The arcsine measure `ω_{[a,b]}` as `π⁻¹` times the Lebesgue measure of the set of `θ` in the
half-circle `(0, π)` with `(a + b)/2 + (b - a)/2 cos θ ∈ E`. -/
lemma arcsineMeasure_eq_volume_Ioo_zero_pi {a b : ℝ} (hab : a < b) {E : Set ℝ}
    (hE : MeasurableSet E) :
    arcsineMeasure a b E =
      ENNReal.ofReal π⁻¹ *
        volume (Ioo 0 π ∩ (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) ⁻¹' E) :=
  arcsineMeasure_eq_of_cos_param hab measurableSet_Ioo
    (fun _ hθ ↦ (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne')
    (injOn_cos_param hab (injOn_cos.mono Ioo_subset_Icc_self))
    (image_cos_param hab (fun _ hθ ↦ (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne')
      fun c hc ↦ ⟨arccos c, ⟨arccos_pos.2 hc.2, arccos_lt_pi.2 hc.1⟩, cos_arccos hc.1.le hc.2.le⟩)
    hE

/-- **Parametrisation of the arcsine measure.** For `a < b`, the arcsine measure `ω_{[a,b]}` is
the image of the uniform probability measure `dθ / 2π` on `[0, 2π)` under
`θ ↦ (a + b)/2 + (b - a)/2 cos θ`. -/
@[zeta5irr "lem_pot_param"]
theorem map_cos_param_eq_arcsineMeasure {a b : ℝ} (hab : a < b) :
    (ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ico 0 (2 * π))).map
      (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) = arcsineMeasure a b := by
  set f : ℝ → ℝ := fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ with hf
  have hfm : Measurable f := by fun_prop
  -- the two halves `(0, π)` and `(π, 2π)` of the circle
  have hsin₂ : ∀ θ ∈ Ioo π (2 * π), sin θ ≠ 0 := fun θ hθ ↦ by
    have := sin_neg_of_neg_of_neg_pi_lt (x := θ - 2 * π) (by linarith [hθ.2]) (by linarith [hθ.1])
    rw [sin_sub_two_pi] at this
    exact this.ne
  have hinj₂ : InjOn cos (Ioo π (2 * π)) := by
    intro x hx y hy hxy
    have := injOn_cos (x₁ := 2 * π - x) (x₂ := 2 * π - y)
      ⟨by linarith [hx.2], by linarith [hx.1]⟩ ⟨by linarith [hy.2], by linarith [hy.1]⟩
      (by simpa [cos_two_pi_sub] using hxy)
    linarith
  have hsurj₂ : ∀ c ∈ Ioo (-1 : ℝ) 1, ∃ θ ∈ Ioo π (2 * π), cos θ = c := fun c hc ↦
    ⟨2 * π - arccos c, ⟨by linarith [arccos_lt_pi.2 hc.1], by linarith [arccos_pos.2 hc.2]⟩,
      by rw [cos_two_pi_sub, cos_arccos hc.1.le hc.2.le]⟩
  ext E hE
  have h₁ := arcsineMeasure_eq_volume_Ioo_zero_pi hab hE
  have h₂ := arcsineMeasure_eq_of_cos_param hab measurableSet_Ioo hsin₂
    (injOn_cos_param hab hinj₂) (image_cos_param hab hsin₂ hsurj₂) hE
  have hsplit : volume (f ⁻¹' E ∩ Ico 0 (2 * π)) =
      volume (Ioo 0 π ∩ f ⁻¹' E) + volume (Ioo π (2 * π) ∩ f ⁻¹' E) := by
    have hae : ∀ {x y : ℝ}, (f ⁻¹' E ∩ Ioc x y : Set ℝ) =ᵐ[volume] (f ⁻¹' E ∩ Ioo x y : Set ℝ) :=
      ae_eq_set_inter (ae_eq_refl _) Ioo_ae_eq_Ioc.symm
    have hae' : (f ⁻¹' E ∩ Ico 0 (2 * π) : Set ℝ) =ᵐ[volume] (f ⁻¹' E ∩ Ioc 0 (2 * π) : Set ℝ) :=
      ae_eq_set_inter (ae_eq_refl _) Ico_ae_eq_Ioc
    rw [measure_congr hae', ← Ioc_union_Ioc_eq_Ioc pi_pos.le (by linarith [pi_pos]),
      inter_union_distrib_left,
      measure_union ((Ioc_disjoint_Ioc_of_le le_rfl).mono inter_subset_right inter_subset_right)
        ((hfm hE).inter measurableSet_Ioc),
      measure_congr hae, measure_congr hae, inter_comm, inter_comm (f ⁻¹' E)]
  rw [Measure.map_apply hfm hE, Measure.smul_apply, Measure.restrict_apply (hfm hE), smul_eq_mul,
    hsplit, mul_inv, ENNReal.ofReal_mul (by norm_num), mul_assoc, mul_add, ← h₁, ← h₂,
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, ← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- Integration against the arcsine measure `ω_{[a,b]}` as an average over a period of the
parametrisation `θ ↦ (a + b)/2 + (b - a)/2 cos θ`. -/
theorem integral_arcsineMeasure_eq {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ u, f u ∂arcsineMeasure a b =
      (2 * π)⁻¹ * ∫ θ in 0..2 * π, f ((a + b) / 2 + (b - a) / 2 * cos θ) := by
  rw [← map_cos_param_eq_arcsineMeasure hab, integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_smul_measure, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity), ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

end Zeta5Irr
