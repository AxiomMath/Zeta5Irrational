/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.EnergyJ
public import Zeta5Irr.RealDeterminant.EnergyGaussSquare
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Nonnegativity of the Gaussian energy `J_ν(s)`

For a finite real signed Borel measure `ν` on `ℂ` and `s > 0`, the Gaussian energy
`J_ν(s) = ∬ exp(-s |z - w|²) dν(z) dν(w)` is nonnegative.

Writing the kernel as a convolution of two Gaussians,
`exp(-s |z - w|²) = (4 s / π) ∫ exp(-2 s |z - u|²) exp(-2 s |w - u|²) dA(u)`, and changing the
order of integration (Fubini) gives
`J_ν(s) = (4 s / π) ∫ (∫ exp(-2 s |z - u|²) dν(z))² dA(u)`,
which is manifestly nonnegative.

## Main results

* `Zeta5Irr.energyJ_eq_integral_sq`: the identity
  `J_ν(s) = (4 s / π) ∫ (∫ exp(-2 s |z - u|²) dν(z))² dA(u)`.
* `Zeta5Irr.energyJ_nonneg`: `0 ≤ J_ν(s)`.

## Implementation notes

* The source assumes `ν` has compact support; this is not needed, since the kernel is bounded
  and a signed measure is finite, so the hypothesis is dropped.
* Fubini is applied to the positive and negative parts of the Jordan decomposition
  `ν = ν⁺ - ν⁻`, where the integrals against `ν` become differences of Bochner integrals.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1: zero-mass logarithmic energy.
-/

@[expose] public section

open MeasureTheory Real

namespace Zeta5Irr

section Auxiliary

variable {s : ℝ}

private lemma integrable_rexp_mul_norm_sub_sq {c : ℝ} (hc : c < 0) (z : ℂ) :
    Integrable (fun u : ℂ => rexp (c * ‖z - u‖ ^ 2)) :=
  Integrable.of_integral_ne_zero <| by
    rw [integral_rexp_mul_norm_sub_sq hc]
    have := Real.pi_pos
    exact (div_pos this (by linarith)).ne'

private lemma rexp_mul_norm_sub_sq_le_one {c : ℝ} (hc : c ≤ 0) (z w : ℂ) :
    rexp (c * ‖z - w‖ ^ 2) ≤ 1 :=
  Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _))

private lemma norm_rexp_mul_norm_sub_sq_le_one {c : ℝ} (hc : c ≤ 0) (z w : ℂ) :
    ‖rexp (c * ‖z - w‖ ^ 2)‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (exp_pos _).le]
  exact rexp_mul_norm_sub_sq_le_one hc z w

private lemma continuous_rexp_mul_norm_sub_sq (c : ℝ) :
    Continuous (fun p : ℂ × ℂ => rexp (c * ‖p.1 - p.2‖ ^ 2)) := by
  fun_prop

/-- The Gaussian kernel is integrable against `μ ⊗ A` for a finite measure `μ`. -/
private lemma integrable_rexp_mul_norm_sub_sq_prod (μ : Measure ℂ) [IsFiniteMeasure μ]
    {c : ℝ} (hc : c < 0) :
    Integrable (fun p : ℂ × ℂ => rexp (c * ‖p.1 - p.2‖ ^ 2)) (μ.prod volume) := by
  rw [integrable_prod_iff (continuous_rexp_mul_norm_sub_sq c).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun z => integrable_rexp_mul_norm_sub_sq hc z, ?_⟩
  simp_rw [Real.norm_of_nonneg (exp_pos _).le, integral_rexp_mul_norm_sub_sq hc]
  exact integrable_const _

/-- The integral of a bounded continuous kernel against a finite measure is continuous. -/
private lemma continuous_integral_of_bound_one (μ : Measure ℂ) [IsFiniteMeasure μ]
    {f : ℂ × ℂ → ℝ} (hf : Continuous f) (hb : ∀ p, ‖f p‖ ≤ 1) :
    Continuous (fun w => ∫ z, f (z, w) ∂μ) :=
  continuous_of_dominated
    (fun _ => (hf.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (fun w => Filter.Eventually.of_forall fun z => hb (z, w)) (integrable_const 1)
    (Filter.Eventually.of_forall fun _ => hf.comp (continuous_const.prodMk continuous_id))

/-- For `c ≤ 0`, the Gaussian kernel `z ↦ exp(c |z - w|²)` is integrable against a finite
measure. -/
private lemma integrable_rexp_mul_norm_sub_sq_of_le (μ : Measure ℂ) [IsFiniteMeasure μ]
    {c : ℝ} (hc : c ≤ 0) (w : ℂ) : Integrable (fun z => rexp (c * ‖z - w‖ ^ 2)) μ :=
  Integrable.of_bound ((continuous_rexp_mul_norm_sub_sq c).comp
    (continuous_id.prodMk continuous_const)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => norm_rexp_mul_norm_sub_sq_le_one hc z w)

/-- `∫ exp(c |z - u|²) dμ(z)`, continuous in `u`, for `c ≤ 0`. -/
private lemma continuous_gaussIntegral (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℝ}
    (hc : c ≤ 0) : Continuous (fun u => ∫ z, rexp (c * ‖z - u‖ ^ 2) ∂μ) :=
  continuous_integral_of_bound_one μ (continuous_rexp_mul_norm_sub_sq _)
    (fun p => norm_rexp_mul_norm_sub_sq_le_one hc p.1 p.2)

private lemma norm_gaussIntegral_le (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℝ} (hc : c ≤ 0)
    (u : ℂ) : ‖∫ z, rexp (c * ‖z - u‖ ^ 2) ∂μ‖ ≤ μ.real Set.univ := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
    (Filter.Eventually.of_forall fun z => norm_rexp_mul_norm_sub_sq_le_one hc z u)

/-- For `c ≤ 0`, `u ↦ ∫ exp(c |z - u|²) dμ(z)` is integrable against a finite measure. -/
private lemma integrable_gaussIntegral_of_le (μ μ' : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] {c : ℝ} (hc : c ≤ 0) :
    Integrable (fun u => ∫ z, rexp (c * ‖z - u‖ ^ 2) ∂μ) μ' :=
  Integrable.of_bound (continuous_gaussIntegral μ hc).aestronglyMeasurable (μ.real Set.univ)
    (Filter.Eventually.of_forall (norm_gaussIntegral_le μ hc))

private lemma integrable_gaussIntegral (μ : Measure ℂ) [IsFiniteMeasure μ] (hs : 0 < s) :
    Integrable (fun u => ∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ) :=
  (integrable_rexp_mul_norm_sub_sq_prod μ (c := -2 * s) (by linarith)).integral_prod_right

private lemma integrable_gaussIntegral_mul (μ μ' : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (hs : 0 < s) :
    Integrable (fun u => (∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ) *
      ∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ') :=
  (integrable_gaussIntegral μ' hs).bdd_mul
    (continuous_gaussIntegral μ (by linarith)).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_gaussIntegral_le μ (by linarith)))

/-- For finite measures `μ, μ'`, the bilinear energy
`∬ exp(-s |z - w|²) dμ(z) dμ'(w)` equals `(4 s / π) ∫ a_μ a_μ' dA`, where
`a_μ(u) = ∫ exp(-2 s |z - u|²) dμ(z)`. -/
private lemma integral_integral_rexp_eq (μ μ' : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (hs : 0 < s) :
    ∫ w, ∫ z, rexp (-s * ‖z - w‖ ^ 2) ∂μ ∂μ' =
      4 * s / π * ∫ u, (∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ) *
        ∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ' := by
  have hc : (-2 * s : ℝ) < 0 := by linarith
  have h1 : ∀ w, ∫ z, rexp (-s * ‖z - w‖ ^ 2) ∂μ =
      4 * s / π * ∫ u, (∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ) * rexp (-2 * s * ‖w - u‖ ^ 2) := by
    intro w
    simp_rw [exp_neg_mul_norm_sub_sq_eq_integral hs _ w]
    rw [integral_const_mul, integral_integral_swap]
    · simp_rw [integral_mul_const]
    · refine (integrable_rexp_mul_norm_sub_sq_prod μ hc).mono
        ((continuous_rexp_mul_norm_sub_sq _).mul
          ((continuous_rexp_mul_norm_sub_sq (-2 * s)).comp
            (continuous_const.prodMk continuous_snd))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      rw [Function.uncurry_def, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_rexp_mul_norm_sub_sq_le_one hc.le w p.2)
  simp_rw [h1]
  rw [integral_const_mul, integral_integral_swap]
  · simp_rw [integral_const_mul]
  · refine ((integrable_rexp_mul_norm_sub_sq_prod μ' hc).const_mul (μ.real Set.univ)).mono
      (((continuous_gaussIntegral μ hc.le).comp continuous_snd).mul
        (continuous_rexp_mul_norm_sub_sq _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Function.uncurry_def, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right ((norm_gaussIntegral_le μ hc.le p.2).trans
      (Real.norm_eq_abs _ ▸ le_abs_self _)) (norm_nonneg _)

/-- Integration against `μ₁ - μ₂` for finite measures is the difference of the integrals. -/
theorem integral_toSignedMeasure_sub_toSignedMeasure {X : Type*} [MeasurableSpace X]
    (μ₁ μ₂ : Measure X) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {f : X → ℝ}
    (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂) :
    ∫ᵛ x, f x ∂<•(μ₁.toSignedMeasure - μ₂.toSignedMeasure) = ∫ x, f x ∂μ₁ - ∫ x, f x ∂μ₂ := by
  rw [VectorMeasure.integral_sub_vectorMeasure, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]
  · simpa [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using h₁
  · simpa [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using h₂

private lemma energyJ_toSignedMeasure_sub (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (hs : 0 < s) :
    energyJ (μ₁.toSignedMeasure - μ₂.toSignedMeasure) s =
      4 * s / π * ∫ u, ((∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ₁) -
        ∫ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂μ₂) ^ 2 := by
  have hc : (-s : ℝ) ≤ 0 := by linarith
  have hK := fun (μ : Measure ℂ) [IsFiniteMeasure μ] w =>
    integrable_rexp_mul_norm_sub_sq_of_le μ hc w
  have hP := fun (μ μ' : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] =>
    integrable_gaussIntegral_of_le μ μ' hc
  simp only [energyJ, integral_toSignedMeasure_sub_toSignedMeasure μ₁ μ₂ (hK μ₁ _) (hK μ₂ _)]
  rw [integral_toSignedMeasure_sub_toSignedMeasure μ₁ μ₂ ((hP μ₁ μ₁).sub' (hP μ₂ μ₁))
    ((hP μ₁ μ₂).sub' (hP μ₂ μ₂)), integral_sub (hP μ₁ μ₁) (hP μ₂ μ₁),
    integral_sub (hP μ₁ μ₂) (hP μ₂ μ₂)]
  simp only [integral_integral_rexp_eq _ _ hs]
  have e : ∀ a b : ℝ, (a - b) ^ 2 = (a * a - b * a) - (a * b - b * b) := by
    intros; ring
  simp_rw [e]
  rw [integral_sub ((integrable_gaussIntegral_mul μ₁ μ₁ hs).sub'
      (integrable_gaussIntegral_mul μ₂ μ₁ hs))
      ((integrable_gaussIntegral_mul μ₁ μ₂ hs).sub' (integrable_gaussIntegral_mul μ₂ μ₂ hs)),
    integral_sub (integrable_gaussIntegral_mul μ₁ μ₁ hs) (integrable_gaussIntegral_mul μ₂ μ₁ hs),
    integral_sub (integrable_gaussIntegral_mul μ₁ μ₂ hs) (integrable_gaussIntegral_mul μ₂ μ₂ hs)]
  ring

end Auxiliary

/-- For a finite real signed measure `ν` on `ℂ` and `s > 0`,
`J_ν(s) = (4 s / π) ∫ (∫ exp(-2 s |z - u|²) dν(z))² dA(u)`. -/
theorem energyJ_eq_integral_sq (ν : SignedMeasure ℂ) {s : ℝ} (hs : 0 < s) :
    energyJ ν s = 4 * s / π * ∫ u, (∫ᵛ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂<•ν) ^ 2 := by
  have key : ∀ j : JordanDecomposition ℂ, energyJ j.toSignedMeasure s =
      4 * s / π * ∫ u, (∫ᵛ z, rexp (-2 * s * ‖z - u‖ ^ 2) ∂<•j.toSignedMeasure) ^ 2 := by
    intro j
    rw [JordanDecomposition.toSignedMeasure, energyJ_toSignedMeasure_sub _ _ hs]
    congr 2 with u
    rw [integral_toSignedMeasure_sub_toSignedMeasure]
    all_goals exact integrable_rexp_mul_norm_sub_sq_of_le _ (by linarith) u
  simpa only [SignedMeasure.toSignedMeasure_toJordanDecomposition] using
    key ν.toJordanDecomposition

/-- **Nonnegativity of the Gaussian energy.** For a finite real signed measure `ν` on `ℂ` and
`s > 0`, `0 ≤ J_ν(s)`. -/
@[zeta5irr "lem_energy_J_nonneg"]
theorem energyJ_nonneg (ν : SignedMeasure ℂ) {s : ℝ} (hs : 0 < s) : 0 ≤ energyJ ν s := by
  rw [energyJ_eq_integral_sq ν hs]
  have := Real.pi_pos
  exact mul_nonneg (by positivity) (integral_nonneg fun u => sq_nonneg _)

end Zeta5Irr
