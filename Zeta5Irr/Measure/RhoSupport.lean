/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Rho
public import Zeta5Irr.Measure.RhoNested

/-!
# The support of `ρ`

The rational arcsine measure `ρ = ∑_{j=1}^{16} cⱼ ω_{[aⱼ, bⱼ]}` is carried by the outermost
interval `[a₁₆, b₁₆]`: each arcsine measure `ω_{[a,b]}` has a density vanishing outside
`(a, b)`, so it gives no mass to the complement of `[a, b]`, and the sixteen intervals are
nested inside `[a₁₆, b₁₆]`.

## Main results

* `Zeta5Irr.arcsineMeasure_compl_Icc`: `ω_{[a,b]}(ℝ ∖ [a, b]) = 0`.
* `Zeta5Irr.rhoA_le_and_le_rhoB`: every interval `[aⱼ, bⱼ]` lies inside `[a₁₆, b₁₆]`.
* `Zeta5Irr.rho_compl_Icc`: `ρ(ℝ ∖ [a₁₆, b₁₆]) = 0`.
* `Zeta5Irr.ae_mem_Icc_arcsineMeasure`, `Zeta5Irr.ae_mem_Icc_rho`: the same statements in
  almost-everywhere form.

## Implementation notes

* The rows are indexed by `Fin 16` starting at `0`, so `a₁₆` is `rhoA 15` and `b₁₆` is
  `rhoB 15`.
* The vanishing of `ω_{[a,b]}` off `[a, b]` holds for all reals `a`, `b`; no ordering is
  needed, and positivity of the weights `cⱼ` is not used.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- The arcsine measure `ω_{[a,b]}` gives no mass to the complement of `[a, b]`. -/
theorem arcsineMeasure_compl_Icc (a b : ℝ) : arcsineMeasure a b (Icc a b)ᶜ = 0 := by
  rw [arcsineMeasure, withDensity_apply _ measurableSet_Icc.compl]
  refine (setLIntegral_eq_zero_iff measurableSet_Icc.compl (by fun_prop)).2 <|
    Filter.Eventually.of_forall fun u hu ↦ arcsinePDF_of_notMem fun h ↦ hu (Ioo_subset_Icc_self h)

/-- Almost every point for the arcsine measure `ω_{[a,b]}` lies in `[a, b]`. -/
theorem ae_mem_Icc_arcsineMeasure (a b : ℝ) : ∀ᵐ t ∂arcsineMeasure a b, t ∈ Icc a b :=
  mem_ae_iff.2 (arcsineMeasure_compl_Icc a b)

/-- Every interval `[aⱼ, bⱼ]` of the table lies inside the outermost one `[a₁₆, b₁₆]`. -/
theorem rhoA_le_and_le_rhoB (j : Fin 16) : rhoA 15 ≤ rhoA j ∧ rhoB j ≤ rhoB 15 :=
  ⟨strictAnti_rhoA.antitone (Fin.le_last j), strictMono_rhoB.monotone (Fin.le_last j)⟩

/-- **The support of `ρ`**: `ρ` gives no mass to the complement of `[a₁₆, b₁₆]`. -/
@[zeta5irr "lem_rho_support"]
theorem rho_compl_Icc : rho (Icc (rhoA 15 : ℝ) (rhoB 15))ᶜ = 0 := by
  rw [rho_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  obtain ⟨ha, hb⟩ := rhoA_le_and_le_rhoB j
  refine mul_eq_zero_of_right _ (measure_mono_null ?_ (arcsineMeasure_compl_Icc _ _))
  exact compl_subset_compl.2 (Icc_subset_Icc (by exact_mod_cast ha) (by exact_mod_cast hb))

/-- Almost every point for `ρ` lies in `[a₁₆, b₁₆]`. -/
theorem ae_mem_Icc_rho : ∀ᵐ t ∂rho, t ∈ Icc (rhoA 15 : ℝ) (rhoB 15) :=
  mem_ae_iff.2 rho_compl_Icc

end Zeta5Irr
