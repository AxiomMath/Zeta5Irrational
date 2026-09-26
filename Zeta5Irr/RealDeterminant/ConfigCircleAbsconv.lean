/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigCircle
public import Zeta5Irr.RealDeterminant.ConfigCirclePotential
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Absolute convergence of the logarithmic potential of a circle

For `c u : ℂ` and `ε > 0`, the function `z ↦ |log |z - u||` is integrable against the uniform
probability measure `ϖ_{c,ε}` on the circle `|z - c| = ε`, and
`∫ |log |z - u|| dϖ_{c,ε}(z) ≤ 2 log⁺ (|c - u| + ε) + |log ε|`.

## Main results

* `Zeta5Irr.CircleIntegrable.integrable_circleUnif`: a circle-integrable function is
  integrable against `ϖ_{c,ε}`.
* `Zeta5Irr.integrable_log_norm_sub_circleUnif`: `z ↦ log |z - u|` is `ϖ_{c,ε}`-integrable.
* `Zeta5Irr.integral_abs_log_norm_sub_circleUnif_le`: the bound
  `∫ |log |z - u|| dϖ_{c,ε}(z) ≤ 2 log⁺ (|c - u| + ε) + |log ε|`.
* `Zeta5Irr.ae_norm_le_circleUnif`: `ϖ_{c,ε}` is carried by the disc of radius `‖c‖ + |ε|`.
* `Zeta5Irr.integrable_log_norm_sub_circleUnif_prod`: `(z, w) ↦ log |z - w|` is integrable
  against `ϖ_{c,ε} ⊗ μ` for every finite measure `μ` carried by a disc.

## Implementation notes

The source states only the inequality, the integral being understood as a possibly infinite
integral of a nonnegative function. Since the Bochner integral of a non-integrable function is
`0`, we also record integrability, which is what makes the inequality meaningful.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

open MeasureTheory Real Set Metric

namespace Zeta5Irr

/-- A function integrable over the circle `|z - c| = |ε|` (in the sense of `CircleIntegrable`) is
integrable against the uniform measure `ϖ_{c,ε}`. -/
theorem CircleIntegrable.integrable_circleUnif {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {c : ℂ} {ε : ℝ} (hf : CircleIntegrable f c ε)
    (hm : AEStronglyMeasurable f (circleUnif c ε)) : Integrable f (circleUnif c ε) := by
  rw [circleUnif, integrable_map_measure hm (measurable_circleMap c ε).aemeasurable]
  refine Integrable.smul_measure ?_ (by simp [pi_pos])
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hf

/-- `z ↦ log |z - u|` is integrable against `ϖ_{c,ε}`. -/
theorem integrable_log_norm_sub_circleUnif (c u : ℂ) (ε : ℝ) :
    Integrable (fun z => log ‖z - u‖) (circleUnif c ε) :=
  CircleIntegrable.integrable_circleUnif (circleIntegrable_log_norm_sub_const ε)
    (by fun_prop : Measurable fun z : ℂ => log ‖z - u‖).aestronglyMeasurable

/-- The absolute logarithmic potential of `ϖ_{c,ε}` is finite and bounded:
`∫ |log |z - u|| dϖ_{c,ε}(z) ≤ 2 log⁺ (|c - u| + ε) + |log ε|`. -/
@[zeta5irr "lem_config_circle_absconv"]
theorem integral_abs_log_norm_sub_circleUnif_le (c u : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z => |log ‖z - u‖|) (circleUnif c ε) ∧
      ∫ z, |log ‖z - u‖| ∂circleUnif c ε ≤ 2 * log⁺ (‖c - u‖ + ε) + |log ε| := by
  have hi := integrable_log_norm_sub_circleUnif c u ε
  refine ⟨hi.abs, ?_⟩
  have hp : Integrable (fun z => log⁺ ‖z - u‖) (circleUnif c ε) := by
    have : (fun z => log⁺ ‖z - u‖) = fun z => (|log ‖z - u‖| + log ‖z - u‖) / 2 := by
      ext z
      rw [← half_mul_log_add_log_abs]
      ring
    rw [this]
    exact (hi.abs.add hi).div_const 2
  have habs : (fun z => |log ‖z - u‖|) = fun z => 2 * log⁺ ‖z - u‖ - log ‖z - u‖ := by
    ext z
    rw [← half_mul_log_add_log_abs]
    ring
  rw [habs, integral_sub (hp.const_mul 2) hi, integral_const_mul,
    integral_log_norm_sub_circleUnif, abs_of_pos hε]
  have h1 : ∫ z, log⁺ ‖z - u‖ ∂circleUnif c ε ≤ log⁺ (‖c - u‖ + ε) := by
    refine (integral_mono_ae hp (integrable_const (log⁺ (‖c - u‖ + ε))) ?_).trans_eq (by simp)
    filter_upwards [ae_mem_sphere_circleUnif c ε] with z hz
    refine posLog_le_posLog (by linarith [norm_nonneg (z - u)]) ?_
    rw [mem_sphere, dist_eq_norm, abs_of_pos hε] at hz
    linarith [norm_sub_le_norm_sub_add_norm_sub z c u]
  linarith [log_le_log hε (le_max_right ‖c - u‖ ε), neg_abs_le (log ε)]

/-- The uniform measure `ϖ_{c,ε}` is carried by the closed disc of radius `‖c‖ + |ε|`. -/
theorem ae_norm_le_circleUnif (c : ℂ) (ε : ℝ) : ∀ᵐ z ∂circleUnif c ε, ‖z‖ ≤ ‖c‖ + |ε| := by
  filter_upwards [ae_mem_sphere_circleUnif c ε] with z hz
  rw [mem_sphere, dist_eq_norm] at hz
  exact hz ▸ norm_le_insert' z c

/-- `(z, w) ↦ log |z - w|` is integrable against `ϖ_{c,ε} ⊗ μ` for every finite measure `μ`
carried by a disc: the inner integral `∫ |log |z - w|| dϖ_{c,ε}(z)` is bounded uniformly for
`w` in the disc. -/
theorem integrable_log_norm_sub_circleUnif_prod {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (hμ : ∀ᵐ w ∂μ, ‖w‖ ≤ R) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) ((circleUnif c ε).prod μ) := by
  have hmeas : StronglyMeasurable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) :=
    (by fun_prop : Measurable fun p : ℂ × ℂ => log ‖p.1 - p.2‖).stronglyMeasurable
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun w => integrable_log_norm_sub_circleUnif c w ε, ?_⟩
  refine Integrable.mono' (integrable_const (2 * log⁺ (‖c‖ + R + ε) + |log ε|))
    (hmeas.norm.integral_prod_left'.aestronglyMeasurable) ?_
  filter_upwards [hμ] with w hw
  obtain ⟨-, hle⟩ := integral_abs_log_norm_sub_circleUnif_le c w hε
  have hcw : ‖c - w‖ ≤ ‖c‖ + R := (norm_sub_le c w).trans (by linarith)
  have hpos : log⁺ (‖c - w‖ + ε) ≤ log⁺ (‖c‖ + R + ε) :=
    posLog_le_posLog (by linarith [norm_nonneg (c - w)]) (by linarith)
  have h0 : 0 ≤ ∫ z, ‖log ‖z - w‖‖ ∂circleUnif c ε := integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_of_nonneg h0]
  simp only [Real.norm_eq_abs]
  linarith

end Zeta5Irr
