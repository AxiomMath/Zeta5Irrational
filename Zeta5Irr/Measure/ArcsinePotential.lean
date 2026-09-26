/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Potential
public import Zeta5Irr.Measure.PotParam
public import Zeta5Irr.Measure.PotChebyshev
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The potential of the arcsine measure on its interval

For reals `a < b` and `t ∈ [a, b]`, the logarithmic potential of the arcsine measure
`ω_{[a,b]}` is constant on the interval: `U^{ω_{[a,b]}}(t) = log ((b - a) / 4)`.

Write `m = (a + b)/2`, `r = (b - a)/2` and `c = (t - m)/r ∈ [-1, 1]`. Since `ω_{[a,b]}` is the
image of `dθ / 2π` on `[0, 2π)` under `θ ↦ m + r cos θ`, and `t - m - r cos θ = r (c - cos θ)`,
the potential is `log r` plus the average of `θ ↦ log |c - cos θ|`. With `μ = e^{i arccos c}`,
a point of the unit circle with `(μ + μ⁻¹)/2 = c`, the Joukowski–Chebyshev identity gives
`log |c - cos θ| = log |e^{iθ} - μ| + log |e^{iθ} - μ⁻¹| - log 2` away from the finitely many
zeros per period of `c - cos θ`, and both circle averages vanish because `|μ| = |μ⁻¹| = 1`.
Hence the potential is `log r - log 2 = log ((b - a)/4)`.

## Main definitions

* `Zeta5Irr.joukowskiPt`: the point `e^{i arccos c}` of the unit circle.

## Main results

* `Zeta5Irr.integral_log_abs_sub_cos`: for `μ ≠ 0` with `(μ + μ⁻¹)/2 = c`,
  `(2π)⁻¹ ∫_0^{2π} log |c - cos θ| dθ = log⁺ |μ| + log⁺ |μ⁻¹| - log 2`.
* `Zeta5Irr.logPotential_arcsineMeasure_eq_posLog`: the resulting formula for the potential
  of `ω_{[a,b]}` at any real point, used both on and off the interval.
* `Zeta5Irr.logPotential_arcsineMeasure`: `U^{ω_{[a,b]}}(t) = log ((b - a)/4)` for
  `t ∈ [a, b]`.
* `Zeta5Irr.integrable_log_abs_sub_arcsineMeasure`: `u ↦ log |t - u|` is integrable against
  `ω_{[a,b]}` for every real `t`.

## Implementation notes

The arcsine measure lives on `ℝ` while the potential is defined for measures on `ℂ`, so the
statement is about the image of `ω_{[a,b]}` under the inclusion `ℝ → ℂ`. The blueprint's
`μ = c + i √(1 - c²)` is written here as `e^{i arccos c}`, which is the same point.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.2 (The arcsine measure and its potential).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real Complex
open scoped ENNReal

/-- For every real `c`, `cos θ ≠ c` for almost every `θ`. -/
lemma ae_cos_ne (c : ℝ) : ∀ᵐ θ : ℝ, Real.cos θ ≠ c := by
  by_cases hc : c ∈ Icc (-1 : ℝ) 1
  swap
  · exact Filter.Eventually.of_forall fun θ h ↦ hc (h ▸ ⟨neg_one_le_cos θ, cos_le_one θ⟩)
  refine ae_iff.2 ?_
  simp only [ne_eq, not_not]
  refine Set.Countable.measure_zero ?_ _
  refine ((countable_range fun k : ℤ ↦ 2 * k * π + arccos c).union
    (countable_range fun k : ℤ ↦ 2 * k * π - arccos c)).mono ?_
  intro θ hθ
  have : Real.cos (arccos c) = Real.cos θ := by rw [cos_arccos hc.1 hc.2]; exact hθ.symm
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.1 this
  · exact Or.inl ⟨k, hk.symm⟩
  · exact Or.inr ⟨k, hk.symm⟩

/-- The Joukowski point `e^{i arccos c}` of `c ∈ [-1, 1]`: a point of the unit circle with
`(μ + μ⁻¹)/2 = c`. -/
noncomputable abbrev joukowskiPt (c : ℝ) : ℂ := exp (arccos c * I)

/-- The Joukowski point lies on the unit circle. -/
lemma norm_joukowskiPt (c : ℝ) : ‖joukowskiPt c‖ = 1 := norm_exp_ofReal_mul_I _

/-- The Joukowski point `μ` of `c ∈ [-1, 1]` satisfies `(μ + μ⁻¹)/2 = c`. -/
lemma joukowskiPt_add_inv {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    (joukowskiPt c + (joukowskiPt c)⁻¹) / 2 = c := by
  rw [joukowskiPt, ← Complex.exp_neg, show -(↑(arccos c) * I) = -↑(arccos c) * I by ring,
    ← Complex.cos, ← ofReal_cos, cos_arccos hc.1 hc.2]

/-- For `μ ≠ 0` with `(μ + μ⁻¹)/2 = c`, almost everywhere
`log |c - cos θ| = log |e^{iθ} - μ| + log |e^{iθ} - μ⁻¹| - log 2`. -/
lemma log_abs_sub_cos_ae_eq {μ : ℂ} (hμ : μ ≠ 0) {c : ℝ} (hc : (μ + μ⁻¹) / 2 = c) :
    (fun θ ↦ Real.log |c - Real.cos θ|) =ᵐ[volume] fun θ ↦
      (((fun z : ℂ ↦ Real.log ‖z - μ‖) + (fun z : ℂ ↦ Real.log ‖z - μ⁻¹‖) -
          fun _ : ℂ ↦ Real.log 2) : ℂ → ℝ)
        (circleMap 0 1 θ) := by
  refine (ae_cos_ne c).mono fun θ hθ ↦ ?_
  have h := norm_joukowski_sub_cos hμ θ
  rw [hc, ← ofReal_sub, norm_real, Real.norm_eq_abs] at h
  have hne : |c - Real.cos θ| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hθ))
  rw [h] at hne
  have h1 : ‖exp (θ * I) - μ‖ ≠ 0 := fun h0 ↦ hne (by rw [h0]; simp)
  have h2 : ‖exp (θ * I) - μ⁻¹‖ ≠ 0 := fun h0 ↦ hne (by rw [h0]; simp)
  simp only [Pi.add_apply, Pi.sub_apply, circleMap, zero_add, ofReal_one, one_mul]
  rw [h, Real.log_div (mul_ne_zero h1 h2) two_ne_zero, Real.log_mul h1 h2]

/-- For every real `c`, `θ ↦ log |c - cos θ|` is integrable over a period. -/
lemma intervalIntegrable_log_abs_sub_cos (c : ℝ) :
    IntervalIntegrable (fun θ ↦ Real.log |c - Real.cos θ|) volume 0 (2 * π) := by
  have h : IntervalIntegrable (fun θ ↦ Real.log (c - Real.cos θ)) volume 0 (2 * π) := by
    apply MeromorphicOn.intervalIntegrable_log
    intro x _
    fun_prop
  simpa only [Real.log_abs] using h

/-- For `μ ≠ 0` with `(μ + μ⁻¹)/2 = c`, the average of `θ ↦ log |c - cos θ|` over a period is
`log⁺ |μ| + log⁺ |μ⁻¹| - log 2`. -/
theorem integral_log_abs_sub_cos {μ : ℂ} (hμ : μ ≠ 0) {c : ℝ} (hc : (μ + μ⁻¹) / 2 = c) :
    (2 * π)⁻¹ * ∫ θ in 0..2 * π, Real.log |c - Real.cos θ| =
      log⁺ ‖μ‖ + log⁺ ‖μ⁻¹‖ - Real.log 2 := by
  have hint := circleIntegrable_log_norm_sub_const (a := μ) (c := 0) 1
  have hint' := circleIntegrable_log_norm_sub_const (a := μ⁻¹) (c := 0) 1
  rw [intervalIntegral.integral_congr_ae ((log_abs_sub_cos_ae_eq hμ hc).mono fun θ h _ ↦ h)]
  refine (circleAverage_sub (hint.add hint') (circleIntegrable_const (Real.log 2) 0 1)).trans ?_
  rw [circleAverage_add hint hint', circleAverage_log_norm_sub_const_eq_posLog,
    circleAverage_log_norm_sub_const_eq_posLog, circleAverage_const]

/-- For reals `a < b` and `t`, and `μ ≠ 0` with `(μ + μ⁻¹)/2 = (t - (a + b)/2) / ((b - a)/2)`,
the potential of `ω_{[a,b]}` at `t` is `log ((b - a)/2) + log⁺ |μ| + log⁺ |μ⁻¹| - log 2`. -/
theorem logPotential_arcsineMeasure_eq_posLog {a b t : ℝ} (hab : a < b) {μ : ℂ} (hμ : μ ≠ 0)
    (hc : (μ + μ⁻¹) / 2 = ((t - (a + b) / 2) / ((b - a) / 2) : ℝ)) :
    logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t =
      Real.log ((b - a) / 2) + log⁺ ‖μ‖ + log⁺ ‖μ⁻¹‖ - Real.log 2 := by
  have hr : 0 < (b - a) / 2 := by linarith
  set c : ℝ := (t - (a + b) / 2) / ((b - a) / 2) with hcdef
  rw [logPotential_map_ofReal, integral_arcsineMeasure_eq hab (by fun_prop)]
  have hcongr : ∫ θ in 0..2 * π, Real.log |t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ)| =
      ∫ θ in 0..2 * π, (Real.log ((b - a) / 2) + Real.log |c - Real.cos θ|) := by
    refine intervalIntegral.integral_congr_ae ((ae_cos_ne c).mono fun θ hθ _ ↦ ?_)
    rw [show t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ) = (b - a) / 2 * (c - Real.cos θ) by
        rw [hcdef, mul_sub, mul_div_cancel₀ _ hr.ne']; ring,
      abs_mul, abs_of_pos hr, Real.log_mul hr.ne' (abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hθ)))]
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegrable_log_abs_sub_cos c), mul_add, integral_log_abs_sub_cos hμ hc,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]
  ring

/-- **Potential of the arcsine measure.** For reals `a < b` and `t ∈ [a, b]`, the logarithmic
potential of the arcsine measure `ω_{[a,b]}`, viewed as a measure on `ℂ`, is
`U^{ω_{[a,b]}}(t) = log ((b - a) / 4)`. -/
@[zeta5irr "lem_arcsine_potential"]
theorem logPotential_arcsineMeasure {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t = Real.log ((b - a) / 4) := by
  have hr : 0 < (b - a) / 2 := by linarith
  have hc1 : (t - (a + b) / 2) / ((b - a) / 2) ∈ Icc (-1 : ℝ) 1 := by
    rw [mem_Icc, le_div_iff₀ hr, div_le_iff₀ hr]
    constructor <;> linarith [ht.1, ht.2]
  rw [logPotential_arcsineMeasure_eq_posLog hab (exp_ne_zero _) (joukowskiPt_add_inv hc1),
    norm_inv, norm_joukowskiPt, inv_one, posLog_one, add_zero, add_zero,
    ← Real.log_div hr.ne' two_ne_zero]
  congr 1
  ring

/-- For reals `a < b` and any real `t`, the function `u ↦ log |t - u|` is integrable against the
arcsine measure `ω_{[a,b]}`. -/
theorem integrable_log_abs_sub_arcsineMeasure {a b : ℝ} (hab : a < b) (t : ℝ) :
    Integrable (fun u ↦ Real.log |t - u|) (arcsineMeasure a b) := by
  have hmeas : Measurable fun u : ℝ ↦ Real.log |t - u| := by fun_prop
  rw [← map_cos_param_eq_arcsineMeasure hab,
    integrable_map_measure hmeas.aestronglyMeasurable (by fun_prop)]
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  have hii : IntervalIntegrable
      (fun θ ↦ Real.log (t - ((a + b) / 2 + (b - a) / 2 * Real.cos θ))) volume 0 (2 * π) := by
    apply MeromorphicOn.intervalIntegrable_log
    intro x _
    fun_prop
  have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 hii
  rw [← integrableOn_Icc_iff_integrableOn_Ioc, integrableOn_Icc_iff_integrableOn_Ico] at hIoc
  simpa only [IntegrableOn, Function.comp_def, Real.log_abs] using hIoc

end Zeta5Irr
