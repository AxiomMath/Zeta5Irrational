/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The logarithmic potential of the uniform measure on a circle

For `c u : ℂ` and `ε > 0`, the logarithmic potential of the uniform probability measure
`ϖ_{c,ε}` on the circle `|z - c| = ε` is
`∫ log |z - u| dϖ_{c,ε}(z) = log (max |c - u| ε)`.

## Main results

* `Zeta5Irr.integral_log_norm_sub_circleUnif`:
  `∫ log ‖z - u‖ dϖ_{c,ε}(z) = log (max ‖c - u‖ |ε|)` for every real `ε`.

## Implementation notes

The source assumes `ε > 0`. The identity holds for every real `ε` with `|ε|` in place of `ε`:
for `ε ≠ 0` it is the mean value of `log ‖· - u‖` over a circle, and for `ε = 0` the measure
`ϖ_{c,0}` is the Dirac mass at `c`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

open MeasureTheory Real

namespace Zeta5Irr

/-- The logarithmic potential of the uniform measure on a circle:
`∫ log ‖z - u‖ dϖ_{c,ε}(z) = log (max ‖c - u‖ |ε|)`. -/
@[zeta5irr "lem_config_circle_potential"]
theorem integral_log_norm_sub_circleUnif (c u : ℂ) (ε : ℝ) :
    ∫ z, log ‖z - u‖ ∂circleUnif c ε = log (max ‖c - u‖ |ε|) := by
  have hm : AEStronglyMeasurable (fun z : ℂ => log ‖z - u‖) (circleUnif c ε) :=
    (by fun_prop : Measurable fun z : ℂ => log ‖z - u‖).aestronglyMeasurable
  rw [integral_circleUnif c ε hm]
  rcases eq_or_ne ε 0 with rfl | hε
  · simp [circleMap_zero_radius]
    field_simp
  change circleAverage (fun z => log ‖z - u‖) c ε = _
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hε]
  have hr : 0 < |ε| := abs_pos.mpr hε
  rw [← posLog_abs, abs_mul, abs_inv, abs_norm, ← log_abs ε]
  rcases le_or_gt ‖c - u‖ |ε| with h | h
  · rw [max_eq_right h, (posLog_eq_zero_iff _).mpr, add_zero]
    rw [abs_of_nonneg (by positivity), inv_mul_le_one₀ hr]
    exact h
  · rw [max_eq_left h.le, posLog_eq_log, log_mul (inv_ne_zero hr.ne') (hr.trans h).ne', log_inv,
      add_neg_cancel_left]
    rw [abs_of_nonneg (by positivity), one_le_inv_mul₀ hr]
    exact h.le

end Zeta5Irr
