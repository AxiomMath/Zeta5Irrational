/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigCircle
public import Zeta5Irr.RealDeterminant.ConfigCircleAbsconv

/-!
# The logarithmic self-energy of a circle

For `c : ℂ` and `ε > 0`, the uniform probability measure `ϖ_{c,ε}` on the circle
`|z - c| = ε` has logarithmic self-energy
`∬ log |z - w| dϖ_{c,ε}(z) dϖ_{c,ε}(w) = log ε`.

The inner integral `∫ log |z - w| dϖ_{c,ε}(z)` is the logarithmic potential
`log (max |c - w| ε)`, which equals `log ε` on the support of `ϖ_{c,ε}`; absolute convergence
comes from the uniform bound on `∫ |log |z - w|| dϖ_{c,ε}(z)` for `w` on the circle.

## Main results

* `Zeta5Irr.integral_log_norm_sub_prod_circleUnif`:
  `∬ log |z - w| dϖ_{c,ε}(z) dϖ_{c,ε}(w) = log ε`.

## Implementation notes

The double integral is the Bochner integral against the product measure. Since the Bochner
integral of a non-integrable function is `0`, the main result also records integrability,
which is what makes the identity meaningful.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

open MeasureTheory Real Set Metric

namespace Zeta5Irr

/-- The logarithmic self-energy of the uniform measure on a circle:
`∬ log |z - w| dϖ_{c,ε}(z) dϖ_{c,ε}(w) = log ε`, the integrand being integrable for
`ϖ_{c,ε} ⊗ ϖ_{c,ε}`. -/
@[zeta5irr "lem_config_self_energy"]
theorem integral_log_norm_sub_prod_circleUnif (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) ((circleUnif c ε).prod (circleUnif c ε)) ∧
      ∫ p : ℂ × ℂ, log ‖p.1 - p.2‖ ∂(circleUnif c ε).prod (circleUnif c ε) = log ε := by
  have hi := integrable_log_norm_sub_circleUnif_prod (ae_norm_le_circleUnif c ε) c hε
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc ∫ x, ∫ y, log ‖(x, y).1 - (x, y).2‖ ∂circleUnif c ε ∂circleUnif c ε
      = ∫ _x, log ε ∂circleUnif c ε := by
        refine integral_congr_ae ?_
        filter_upwards [ae_mem_sphere_circleUnif c ε] with x hx
        rw [mem_sphere, dist_eq_norm, abs_of_pos hε] at hx
        simp only [norm_sub_rev x]
        rw [integral_log_norm_sub_circleUnif, norm_sub_rev c x, hx, abs_of_pos hε, max_self]
    _ = log ε := by simp

end Zeta5Irr
