/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigCircle
public import Zeta5Irr.RealDeterminant.ConfigCircleAbsconv
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The mutual logarithmic energy of two circles

For `c c' : ℂ` and `ε > 0`, the mutual logarithmic energy of the uniform probability measures
`ϖ_{c,ε}` and `ϖ_{c',ε}` on the circles of radius `ε` about `c` and `c'` is bounded below by
the logarithm of the regularised distance of the centres:
`log (max |c - c'| ε) ≤ ∬ log |z - w| dϖ_{c,ε}(z) dϖ_{c',ε}(w)`.

The double integral converges absolutely: for `w` on the circle about `c'`, the absolute
logarithmic potential of `ϖ_{c,ε}` at `w` is bounded independently of `w`. By Fubini's theorem
it is an iterated integral; the inner integral is the logarithmic potential
`log (max |z - c'| ε) ≥ log |z - c'|` of the circle about `c'`, and integrating
`log |z - c'|` against `ϖ_{c,ε}` gives `log (max |c - c'| ε)`.

## Main results

* `Zeta5Irr.circleUnif_singleton`: `ϖ_{c,ε}` has no atoms for `ε ≠ 0`.
* `Zeta5Irr.integrable_log_norm_sub_circleUnif_prod_circleUnif`: `(z, w) ↦ log |z - w|` is
  integrable against `ϖ_{c,ε} ⊗ ϖ_{c',ε}`.
* `Zeta5Irr.log_max_norm_sub_le_integral_log_norm_sub_prod_circleUnif`: the lower bound
  `log (max |c - c'| ε) ≤ ∬ log |z - w| dϖ_{c,ε}(z) dϖ_{c',ε}(w)`.

## Implementation notes

The double integral is the Bochner integral against the product measure
`ϖ_{c,ε} ⊗ ϖ_{c',ε}`. Since a non-integrable function has Bochner integral `0`, we record
the absolute convergence as a separate integrability statement. The pointwise comparison
`log (max |z - c'| ε) ≥ log |z - c'|` fails at `z = c'` under the convention `log 0 = 0`;
it holds `ϖ_{c,ε}`-almost everywhere because `ϖ_{c,ε}` has no atoms.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

open MeasureTheory Real Set Metric

namespace Zeta5Irr

/-- The uniform measure `ϖ_{c,ε}` on a circle of nonzero radius has no atoms. -/
theorem circleUnif_singleton (c u : ℂ) {ε : ℝ} (hε : ε ≠ 0) : circleUnif c ε {u} = 0 := by
  rw [circleUnif, Measure.map_apply (measurable_circleMap c ε) (measurableSet_singleton u),
    Measure.smul_apply, smul_eq_mul]
  have h : volume.restrict (Ioc (0 : ℝ) (2 * π)) (circleMap c ε ⁻¹' {u}) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans_eq
      (((Set.countable_singleton u).preimage_circleMap c hε).measure_zero volume))
  rw [h, mul_zero]

/-- The mutual logarithmic energy of two circles converges absolutely:
`(z, w) ↦ log |z - w|` is integrable against `ϖ_{c,ε} ⊗ ϖ_{c',ε}`. -/
theorem integrable_log_norm_sub_circleUnif_prod_circleUnif (c c' : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) ((circleUnif c ε).prod (circleUnif c' ε)) :=
  integrable_log_norm_sub_circleUnif_prod (ae_norm_le_circleUnif c' ε) c hε

/-- The mutual logarithmic energy of the uniform measures on two circles of radius `ε > 0`
is bounded below by the logarithm of the regularised distance of their centres:
`log (max |c - c'| ε) ≤ ∬ log |z - w| dϖ_{c,ε}(z) dϖ_{c',ε}(w)`. -/
@[zeta5irr "lem_config_mutual"]
theorem log_max_norm_sub_le_integral_log_norm_sub_prod_circleUnif (c c' : ℂ) {ε : ℝ}
    (hε : 0 < ε) :
    log (max ‖c - c'‖ ε) ≤
      ∫ p, log ‖p.1 - p.2‖ ∂(circleUnif c ε).prod (circleUnif c' ε) := by
  have hi := integrable_log_norm_sub_circleUnif_prod_circleUnif c c' hε
  rw [integral_prod _ hi]
  have hinner : ∀ z : ℂ, ∫ w, log ‖z - w‖ ∂circleUnif c' ε = log (max ‖c' - z‖ ε) := by
    intro z
    simp_rw [norm_sub_rev z]
    rw [integral_log_norm_sub_circleUnif, abs_of_pos hε]
  calc log (max ‖c - c'‖ ε) = ∫ z, log ‖z - c'‖ ∂circleUnif c ε := by
        rw [integral_log_norm_sub_circleUnif, abs_of_pos hε]
    _ ≤ ∫ z, ∫ w, log ‖z - w‖ ∂circleUnif c' ε ∂circleUnif c ε := by
        refine integral_mono_ae (integrable_log_norm_sub_circleUnif c c' ε)
          hi.integral_prod_left ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp (circleUnif_singleton c c' hε.ne')]
          with z hz
        rw [hinner z, norm_sub_rev]
        exact log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))) (le_max_left _ _)

end Zeta5Irr
