/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.ArcsinePotential
public import Zeta5Irr.Measure.RhoSupport

/-!
# Mutual energies of the sixteen arcsine measures

For `1 ≤ k ≤ j ≤ 16` the intervals are nested, `[a_k, b_k] ⊆ [a_j, b_j]`, so the potential of
`ω_{[a_j,b_j]}` is the constant `log ((b_j - a_j)/4)` on the support of `ω_{[a_k,b_k]}`.
Integrating this constant against the probability measure `ω_{[a_k,b_k]}` gives
`∬ log |t - u| dω_{[a_k,b_k]}(t) dω_{[a_j,b_j]}(u) = log ((b_j - a_j)/4)`.

## Main results

* `Zeta5Irr.integral_integral_log_abs_sub_arcsineMeasure`: for `a < b` and `a ≤ c < d ≤ b`,
  `∫ t, ∫ u, log |t - u| dω_{[a,b]}(u) dω_{[c,d]}(t) = log ((b - a)/4)`.
* `Zeta5Irr.integral_integral_log_abs_sub_rho`: for `k ≤ j`,
  `∬ log |t - u| dω_{[a_k,b_k]}(t) dω_{[a_j,b_j]}(u) = log ((b_j - a_j)/4)`.

## Implementation notes

* The double integral of the source is written as the iterated integral, inner integral in `u`
  against `ω_{[a_j,b_j]}`, which is how the source evaluates it.
* The rows are indexed by `Fin 16` starting at `0`, so `a_j` of the source is `rhoA (j - 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- For `a < b` and `t ∈ [a, b]`, `∫ log |t - u| dω_{[a,b]}(u) = log ((b - a)/4)`: the real form
of `logPotential_arcsineMeasure`. -/
theorem integral_log_abs_sub_arcsineMeasure {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    ∫ u, Real.log |t - u| ∂arcsineMeasure a b = Real.log ((b - a) / 4) := by
  rw [← logPotential_arcsineMeasure hab ht, logPotential_map_ofReal]

/-- For `a < b` and `a ≤ c < d ≤ b`, the mutual logarithmic energy of the arcsine measures
`ω_{[c,d]}` and `ω_{[a,b]}` is `log ((b - a)/4)`. -/
theorem integral_integral_log_abs_sub_arcsineMeasure {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    ∫ t, ∫ u, Real.log |t - u| ∂arcsineMeasure a b ∂arcsineMeasure c d =
      Real.log ((b - a) / 4) := by
  have := isProbabilityMeasure_arcsineMeasure hcd
  rw [integral_congr_ae ((ae_mem_Icc_arcsineMeasure c d).mono fun t ht ↦
    integral_log_abs_sub_arcsineMeasure hab ⟨hac.trans ht.1, ht.2.trans hdb⟩), integral_const,
    probReal_univ, one_smul]

/-- **Mutual energies of the sixteen arcsine measures.** For `1 ≤ k ≤ j ≤ 16`,
`∬ log |t - u| dω_{[a_k,b_k]}(t) dω_{[a_j,b_j]}(u) = log ((b_j - a_j)/4)`. -/
@[zeta5irr "lem_rho_mutual"]
theorem integral_integral_log_abs_sub_rho {j k : Fin 16} (hkj : k ≤ j) :
    ∫ t, ∫ u, Real.log |t - u| ∂arcsineMeasure (rhoA j) (rhoB j)
      ∂arcsineMeasure (rhoA k) (rhoB k) = Real.log (((rhoB j : ℝ) - rhoA j) / 4) :=
  integral_integral_log_abs_sub_arcsineMeasure (rhoA_lt_rhoB_real j)
    (rhoA_lt_rhoB_real k)
    (by exact_mod_cast strictAnti_rhoA.antitone hkj)
    (by exact_mod_cast strictMono_rhoB.monotone hkj)

end Zeta5Irr
