/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Measure.Potential
public import Zeta5Irr.Measure.Rho
public import Zeta5Irr.Measure.RhoMass
public import Zeta5Irr.Measure.RhoSupport

/-!
# The potential of `ρ` far to the right

For `t ≥ 2` the logarithmic potential of the rational arcsine measure `ρ` satisfies
`U^ρ(t) ≤ λ log t`. The measure `ρ` is carried by `[a₁₆, b₁₆] ⊆ (0, 2)`, so for `ρ`-almost
every `u` we have `0 < t - u < t` and hence `log |t - u| ≤ log t`; integrating against `ρ`,
whose total mass is `λ`, gives the bound.

## Main results

* `Zeta5Irr.logPotential_rho_le`: for `t ≥ 2`, `U^ρ(t) ≤ λ log t`.

## Implementation notes

* The measure `ρ` lives on `ℝ`; its potential is that of the pushforward of `ρ` to `ℂ`
  along the inclusion `ℝ → ℂ`, evaluated at the real point `t`.
* The potential is a Bochner integral, which is `0` when the integrand is not integrable;
  since `log t > 0` for `t ≥ 2`, the bound holds in that case as well.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- **The potential of `ρ` far to the right**: for `t ≥ 2`, `U^ρ(t) ≤ λ log t`. -/
@[zeta5irr "lem_rho_pot_far"]
theorem logPotential_rho_le {t : ℝ} (ht : 2 ≤ t) :
    logPotential (rho.map ((↑) : ℝ → ℂ)) t ≤ (orderRatio : ℝ) * Real.log t := by
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  rw [logPotential_map_ofReal]
  by_cases hint : Integrable (fun u ↦ Real.log |t - u|) rho
  · calc ∫ u, Real.log |t - u| ∂rho ≤ ∫ _, Real.log t ∂rho := by
          refine integral_mono_ae hint (integrable_const _) (ae_mem_Icc_rho.mono fun u hu ↦ ?_)
          have h0 : (0 : ℝ) < rhoA 15 := by exact_mod_cast rhoA_fifteen_pos
          have h2 : (rhoB 15 : ℝ) < 2 := by exact_mod_cast rhoB_fifteen_lt_two
          have hu0 : 0 < u := h0.trans_le hu.1
          have hu2 : u < 2 := hu.2.trans_lt h2
          change Real.log |t - u| ≤ Real.log t
          rw [abs_of_pos (by linarith)]
          exact Real.log_le_log (by linarith) (by linarith)
      _ = (orderRatio : ℝ) * Real.log t := by
          rw [integral_const, smul_eq_mul, rho_real_univ]
  · rw [integral_undef hint]
    exact mul_nonneg (by norm_num [orderRatio]) hlog.le

end Zeta5Irr
