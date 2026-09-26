/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Potential
public import Zeta5Irr.Measure.Rho
public import Zeta5Irr.Measure.RhoEnergyFormula
public import Zeta5Irr.RealDeterminant.ConfigCircle
public import Zeta5Irr.RealDeterminant.ConfigIntegrable
public import Zeta5Irr.RealDeterminant.ConfigPotentialFinite
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Smoothing the potential of `ρ` over a small circle

Averaging the logarithmic potential `U^ρ` of the arcsine measure `ρ` over the circle
`|z - t| = ε` raises it by at most `60 √ε`:
`∫ U^ρ dϖ_{t,ε} - U^ρ(t) ≤ 60 √ε`.

The proof applies Fubini's theorem to `(z, u) ↦ log |z - u|` on `ϖ_{t,ε} ⊗ ρ`, evaluates the
inner circle average as `log max(|t - u|, ε)`, rewrites the difference with `U^ρ(t)` as
`∫ log⁺ (ε / |t - u|) dρ(u)`, and bounds that by the layer-cake formula and the estimate
`ρ(disc of radius r) ≤ 28 √r`, which give `∫₀^ε 28 r^{-1/2} dr = 56 √ε`.

## Main results

* `Zeta5Irr.integral_logPotential_rho_circleUnif_sub_le`: for every `t` and `ε > 0`,
  `∫ U^ρ dϖ_{t,ε} - U^ρ(t) ≤ 60 √ε`.

## Implementation notes

* The source takes `t ∈ [0, ∞)`; the argument works verbatim for every `t ∈ ℂ`, and the
  statement is proved in that generality.
* `ρ` is a measure on `ℝ`; its potential is that of the pushforward `ρ` on `ℂ`, as elsewhere
  in the project.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Real Set

/-- `log max(d, ε) - log d = log⁺ (ε / d)` for `d, ε > 0`. -/
private lemma log_max_sub_log {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    log (max d ε) - log d = log⁺ (ε / d) := by
  rcases le_total ε d with h | h
  · rw [max_eq_left h, sub_self, (posLog_eq_zero_iff _).2]
    rw [abs_of_pos (by positivity)]
    exact (div_le_one hd).2 h
  · have h1 : 1 ≤ |ε / d| := by rw [abs_of_pos (by positivity)]; exact (one_le_div hd).2 h
    rw [max_eq_right h, posLog_eq_log h1, log_div hε.ne' hd.ne']

/-- **Smoothing the potential of `ρ` over a circle.** For every `t ∈ ℂ` and every `ε > 0`,
`∫ U^ρ(z) dϖ_{t,ε}(z) - U^ρ(t) ≤ 60 √ε`. -/
@[zeta5irr "lem_config_error"]
theorem integral_logPotential_rho_circleUnif_sub_le (t : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, logPotential (rho.map ((↑) : ℝ → ℂ)) z ∂circleUnif t ε -
      logPotential (rho.map ((↑) : ℝ → ℂ)) t ≤ 60 * √ε := by
  set ϖ := circleUnif t ε
  set F : ℂ × ℝ → ℝ := fun p => log ‖p.1 - p.2‖
  -- `F` is integrable on `ϖ ⊗ ρ`
  have hF : Integrable F (ϖ.prod rho) := by
    have h := integrable_log_norm_sub_circleUnif_prod ae_norm_le_two_rho_map t hε
    rw [← Measure.map_id (μ := circleUnif t ε), Measure.map_prod_map _ _ measurable_id
      Complex.measurable_ofReal, integrable_map_measure
      (by fun_prop : Measurable fun p : ℂ × ℂ => log ‖p.1 - p.2‖).aestronglyMeasurable
      (measurable_id.prodMap Complex.measurable_ofReal).aemeasurable] at h
    exact h
  -- Fubini and the circle potential
  have hswap : ∫ z, logPotential (rho.map ((↑) : ℝ → ℂ)) z ∂ϖ =
      ∫ u : ℝ, log (max ‖t - u‖ ε) ∂rho := by
    simp_rw [logPotential_map_ofReal_eq_integral_norm]
    rw [integral_integral_swap hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [ϖ, integral_log_norm_sub_circleUnif, abs_of_pos hε]
  have hg1 : Integrable (fun u : ℝ => log (max ‖t - u‖ ε)) rho := by
    refine hF.integral_prod_right.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [F]
    rw [integral_log_norm_sub_circleUnif, abs_of_pos hε]
  -- the difference is `∫ log⁺ (ε / |t - u|) dρ`
  set h : ℝ → ℝ := fun u => log⁺ (ε / ‖t - u‖)
  have hh0 : 0 ≤ h := fun u => posLog_nonneg
  have hhl : ∫⁻ u, ENNReal.ofReal (h u) ∂rho ≤ ENNReal.ofReal (56 * √ε) :=
    (lintegral_mono fun u => by simp only [h]; split_ifs <;> simp).trans
      (lintegral_ite_posLog_div_rho_le t hε)
  have hh : Integrable h rho := by
    refine ⟨(by fun_prop : Measurable h).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hh0)]
    exact hhl.trans_lt ENNReal.ofReal_lt_top
  have hne : ∀ᵐ u : ℝ ∂rho, t ≠ (u : ℂ) := by
    refine measure_mono_null (fun u (hu : ¬ t ≠ (u : ℂ)) => ?_) (rho_singleton t.re)
    rw [not_not] at hu
    simp [hu]
  have hdiff : (fun u : ℝ => log (max ‖t - u‖ ε) - log ‖t - u‖) =ᵐ[rho] h := by
    filter_upwards [hne] with u hu
    exact log_max_sub_log (norm_pos_iff.2 (sub_ne_zero.2 hu)) hε
  have hg2 : Integrable (fun u : ℝ => log ‖t - u‖) rho :=
    (hg1.sub hh).congr (by
      filter_upwards [hdiff] with u hu
      simp only [Pi.sub_apply]
      linarith)
  rw [hswap, logPotential_map_ofReal_eq_integral_norm, ← integral_sub hg1 hg2,
    integral_congr_ae hdiff,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh0)
      (by fun_prop : Measurable h).aestronglyMeasurable]
  calc (∫⁻ u, ENNReal.ofReal (h u) ∂rho).toReal ≤ (ENNReal.ofReal (56 * √ε)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hhl
    _ = 56 * √ε := ENNReal.toReal_ofReal (by positivity)
    _ ≤ 60 * √ε := by gcongr; norm_num

end Zeta5Irr
