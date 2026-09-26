/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.EnergyJ
public import Zeta5Irr.RealDeterminant.EnergyLab
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.VectorMeasure.Prod
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# The double integral of `L_{a,b}` against a zero-mass signed measure

Let `ν` be a finite real signed measure on `ℂ` with total mass `ν(ℂ) = 0`, and let `a, b > 0`.
Integrating the truncated logarithmic kernel `L_{a,b}(|z - w|)` against `ν ⊗ ν` gives
`∬ L_{a,b}(|z - w|) dν(z) dν(w) = -½ ∫_a^b J_ν(s) / s ds`,
where `J_ν(s) = ∬ exp(-s |z - w|²) dν(z) dν(w)` is the Gaussian energy.

The proof exchanges the `s`-integral defining `L_{a,b}` with the two integrals against `ν`
(Fubini's theorem; the integrand is bounded by `1 / a` and all measures involved are finite).
For fixed `s`, the term `exp(-s)` integrates to `exp(-s) ν(ℂ)² = 0`, and the remaining term is
`J_ν(s)`.

## Main results

* `Zeta5Irr.integral_integral_energyLab`: the identity above, for `a, b > 0`.
* `Zeta5Irr.integral_integral_energyLab_of_le`: the same identity for `0 < a ≤ b`.

## Implementation notes

* The source assumes `ν` has compact support and `a < b`. Neither is needed: the kernel
  `(e^{-s} - e^{-s r²}) / s` is bounded by `1 / min a b` for `s` between `a` and `b`, so every
  finite signed measure is admissible, and both sides are oriented integrals in `a, b`.
* The double integrals are iterated integrals against `ν`, integrating first in `z` and then
  in `w`, as in the definition of `Zeta5Irr.energyJ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1 (Zero-mass logarithmic energy).
-/

@[expose] public section

open MeasureTheory VectorMeasure Real Set Filter

namespace Zeta5Irr

/-- For `m > 0` and `x ≥ 0`, `|(e^{-m} - e^{-m x}) / m| ≤ 1 / m`. -/
theorem abs_exp_neg_sub_exp_neg_mul_div_le {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    |(exp (-m) - exp (-m * x)) / m| ≤ 1 / m := by
  rw [abs_div, abs_of_pos hm]
  gcongr
  have h1 : exp (-m) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have h2 : exp (-m * x) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have h3 := exp_pos (-m)
  have h4 := exp_pos (-m * x)
  rw [abs_le]
  constructor <;> linarith

/-- **Double integral of `L_{a,b}`**, for `0 < a ≤ b`: if `ν(ℂ) = 0`, then
`∬ L_{a,b}(|z - w|) dν(z) dν(w) = -½ ∫_a^b J_ν(s) / s ds`. -/
theorem integral_integral_energyLab_of_le (ν : SignedMeasure ℂ) (hν : ν univ = 0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ᵛ w, ∫ᵛ z, energyLab a b ‖z - w‖ ∂<•ν ∂<•ν =
      -(1 / 2) * ∫ s in a..b, energyJ ν s / s := by
  have : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance
  set l : SignedMeasure ℝ := (volume.restrict (Ioc a b)).toSignedMeasure with hl_def
  have hl : l.variation = volume.restrict (Ioc a b) := Measure.variation_toSignedMeasure
  have : IsFiniteMeasure l.variation := by rw [hl]; infer_instance
  set k : ℝ → ℂ → ℂ → ℝ := fun s z w =>
    (exp (-max a s) - exp (-max a s * ‖z - w‖ ^ 2)) / max a s with hk
  have hk_meas : Measurable (fun p : (ℂ × ℝ) × ℂ => k p.1.2 p.2 p.1.1) := by
    simp only [hk]; fun_prop
  have hk_bound : ∀ s z w, ‖k s z w‖ ≤ 1 / a := by
    intro s z w
    have hm : 0 < max a s := lt_max_of_lt_left ha
    rw [Real.norm_eq_abs]
    exact (abs_exp_neg_sub_exp_neg_mul_div_le hm (by positivity)).trans
      (one_div_le_one_div_of_le ha (le_max_left a s))
  have h1 : ∀ z w, energyLab a b ‖z - w‖ = (1 / 2 : ℝ) • ∫ᵛ s, k s z w ∂<•l := by
    intro z w
    rw [energyLab, hl_def, integral_toSignedMeasure, intervalIntegral.integral_of_le hab,
      smul_eq_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [hk, max_eq_right hs.1.le]
  have h2 : ∀ w, ∫ᵛ z, ∫ᵛ s, k s z w ∂<•l ∂<•ν = ∫ᵛ s, ∫ᵛ z, k s z w ∂<•ν ∂<•l := by
    intro w
    refine integral_integral_swap (f := fun z s => k s z w) ?_ ?_
    swap; · intros; simp; ring
    refine Integrable.of_bound ?_ (1 / a) (Eventually.of_forall fun p => hk_bound _ _ _)
    exact (hk_meas.comp (by fun_prop : Measurable fun p : ℂ × ℝ => ((w, p.2), p.1)))
      |>.aestronglyMeasurable
  have h3 : ∫ᵛ w, ∫ᵛ s, (∫ᵛ z, k s z w ∂<•ν) ∂<•l ∂<•ν =
      ∫ᵛ s, ∫ᵛ w, ∫ᵛ z, k s z w ∂<•ν ∂<•ν ∂<•l := by
    refine integral_integral_swap (f := fun w s => ∫ᵛ z, k s z w ∂<•ν) ?_ ?_
    swap; · intros; simp; ring
    refine Integrable.of_bound ?_
      (1 / a * ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ *
        ν.variation.real univ) (Eventually.of_forall fun p => ?_)
    · exact (StronglyMeasurable.integral_vectorMeasure_prod_right
        (f := fun (p : ℂ × ℝ) z => k p.2 z p.1) hk_meas.stronglyMeasurable).aestronglyMeasurable
    · exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun z => hk_bound _ _ _)
  have h4 : ∀ s ∈ Ioc a b, ∫ᵛ w, ∫ᵛ z, k s z w ∂<•ν ∂<•ν = -(energyJ ν s / s) := by
    intro s hs
    have hinner : ∀ w, ∫ᵛ z, k s z w ∂<•ν =
        -(s⁻¹ • ∫ᵛ z, exp (-s * ‖z - w‖ ^ 2) ∂<•ν) := by
      intro w
      have hint : ν.Integrable (fun z => exp (-s * ‖z - w‖ ^ 2)) := by
        refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_one_iff.mpr (by nlinarith [hs.1, norm_nonneg (z - w)])
      have : (fun z => k s z w) =
          fun z => s⁻¹ • (exp (-s) - exp (-s * ‖z - w‖ ^ 2)) := by
        ext z
        simp only [hk, max_eq_right hs.1.le, smul_eq_mul]
        ring
      rw [this, integral_fun_smul, integral_fun_sub (integrable_const _) hint,
        VectorMeasure.integral_const, hν]
      simp
    simp_rw [hinner]
    rw [integral_fun_neg, integral_fun_smul, energyJ, smul_eq_mul, div_eq_inv_mul]
  calc ∫ᵛ w, ∫ᵛ z, energyLab a b ‖z - w‖ ∂<•ν ∂<•ν
      = (1 / 2 : ℝ) • ∫ᵛ s, ∫ᵛ w, ∫ᵛ z, k s z w ∂<•ν ∂<•ν ∂<•l := by
        simp_rw [h1, integral_fun_smul, h2]
        rw [h3]
    _ = (1 / 2 : ℝ) • ∫ᵛ s, -(energyJ ν s / s) ∂<•l := by
        congr 1
        apply VectorMeasure.integral_congr_ae
        rw [hl]
        exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall h4)
    _ = -(1 / 2) * ∫ s in a..b, energyJ ν s / s := by
        rw [integral_fun_neg, hl_def, integral_toSignedMeasure,
          intervalIntegral.integral_of_le hab, smul_eq_mul]
        ring

/-- **Double integral of `L_{a,b}`** (Fauzan, §10.1): for a finite real signed measure `ν` on
`ℂ` with `ν(ℂ) = 0` and `a, b > 0`,
`∬ L_{a,b}(|z - w|) dν(z) dν(w) = -½ ∫_a^b J_ν(s) / s ds`. -/
@[zeta5irr "lem_energy_Lab_double"]
theorem integral_integral_energyLab (ν : SignedMeasure ℂ) (hν : ν univ = 0) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ᵛ w, ∫ᵛ z, energyLab a b ‖z - w‖ ∂<•ν ∂<•ν =
      -(1 / 2) * ∫ s in a..b, energyJ ν s / s := by
  rcases le_total a b with h | h
  · exact integral_integral_energyLab_of_le ν hν ha h
  · simp_rw [energyLab_symm b a, integral_fun_neg]
    rw [integral_integral_energyLab_of_le ν hν hb h, intervalIntegral.integral_symm a b]
    ring

end Zeta5Irr
