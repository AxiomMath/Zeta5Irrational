/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Rho
public import Zeta5Irr.RealDeterminant.ConfigLayerCake
public import Zeta5Irr.RealDeterminant.ConfigRhoBall
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The `log⁺` potential of `ρ` is bounded

For every `z ∈ ℂ`, `∫ log⁺ (1 / |z - u|) dρ(u) ≤ 56`. By the layer-cake formula with `δ = 1`
the left side equals `∫₀¹ ρ {u : |z - u| < r} / r dr`, and the numerator is at most `28 √r`,
so the integral is at most `∫₀¹ 28 r^(-1/2) dr = 56`.

## Main results

* `Zeta5Irr.lintegral_Ioo_rpow_neg_half`: `∫₀^ε 28 r^{-1/2} dr = 56 √ε`.
* `Zeta5Irr.lintegral_ite_posLog_div_rho_le`: `∫ log⁺ (ε / |z - u|) dρ(u) ≤ 56 √ε`.
* `Zeta5Irr.lintegral_posLog_rho_le`: `∫ log⁺ (1 / |z - u|) dρ(u) ≤ 56`.

## Implementation notes

* The integral is a lower Lebesgue integral in `ℝ≥0∞`, and the integrand at `u = z`, where
  `log⁺ (1 / 0)` is read as `+∞`, is `⊤`, as in the layer-cake formula.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

/-- `∫₀^ε 28 r^{-1/2} dr = 56 √ε`, as a lower Lebesgue integral. -/
theorem lintegral_Ioo_rpow_neg_half {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ r in Ioo (0 : ℝ) ε, ENNReal.ofReal (28 * r ^ (-(1 / 2) : ℝ)) =
      ENNReal.ofReal (56 * √ε) := by
  have hint : IntegrableOn (fun r : ℝ => 28 * r ^ (-(1 / 2) : ℝ)) (Ioo 0 ε) := by
    have : IntervalIntegrable (fun r : ℝ => 28 * r ^ (-(1 / 2) : ℝ)) volume 0 ε :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hε.le] at this
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε.le,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
      sqrt_eq_rpow]
    congr 1
    norm_num
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have := rpow_nonneg hr.1.le (-(1 / 2) : ℝ)
    positivity

/-- For every `z ∈ ℂ` and `ε > 0`, `∫ log⁺ (ε / |z - u|) dρ(u) ≤ 56 √ε`, where
`log⁺ (ε / 0) = ∞`. -/
theorem lintegral_ite_posLog_div_rho_le (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ u, (if z = u then ⊤ else ENNReal.ofReal (posLog (ε / ‖z - u‖))) ∂rho ≤
      ENNReal.ofReal (56 * √ε) := by
  rw [lintegral_posLog_eq_lintegral_measure_div rho z hε]
  calc ∫⁻ r in Ioo 0 ε, rho {u | ‖z - u‖ < r} / ENNReal.ofReal r
      ≤ ∫⁻ r in Ioo (0 : ℝ) ε, ENNReal.ofReal (28 * r ^ (-(1 / 2) : ℝ)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        refine (ENNReal.div_le_div_right (rho_ball_le z r) _).trans ?_
        rw [← ENNReal.ofReal_div_of_pos hr.1]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [sqrt_eq_rpow, mul_div_assoc, div_eq_mul_inv, ← rpow_neg_one,
          ← rpow_add hr.1]
        norm_num
    _ = ENNReal.ofReal (56 * √ε) := lintegral_Ioo_rpow_neg_half hε

/-- **The `log⁺` potential of `ρ` is bounded.** For every `z ∈ ℂ`,
`∫ log⁺ (1 / |z - u|) dρ(u) ≤ 56`, where `log⁺ (1 / 0) = ∞`. -/
@[zeta5irr "lem_config_potential_finite"]
theorem lintegral_posLog_rho_le (z : ℂ) :
    ∫⁻ u, (if z = u then ⊤ else ENNReal.ofReal (posLog (1 / ‖z - u‖))) ∂rho ≤ 56 := by
  simpa using lintegral_ite_posLog_div_rho_le z one_pos

end Zeta5Irr
