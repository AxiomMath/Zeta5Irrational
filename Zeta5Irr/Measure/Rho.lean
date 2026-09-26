/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Arcsine
public import Zeta5Irr.Measure.RhoNested

/-!
# The rational arcsine measure `ρ`

The comparison measure of §9.3 is the positive combination of sixteen arcsine measures
`ρ = ∑_{j=1}^{16} cⱼ ω_{[aⱼ, bⱼ]}`, where `aⱼ`, `bⱼ`, `cⱼ` are the rationals of Table 1
and `ω_{[a,b]}` is the arcsine measure of the interval `[a, b]`.

## Main definitions

* `Zeta5Irr.rho`: the measure `ρ = ∑ⱼ cⱼ ω_{[aⱼ, bⱼ]}` on `ℝ`.

## Main results

* `Zeta5Irr.rho_apply`: the mass `ρ(s) = ∑ⱼ cⱼ ω_{[aⱼ, bⱼ]}(s)` of a set.
* `Zeta5Irr.rho_univ`: the total mass of `ρ` is `∑ⱼ cⱼ`.
* `Zeta5Irr.isFiniteMeasure_rho`: `ρ` is a finite measure.

## Implementation notes

* The rows of the table are indexed by `Fin 16` starting at `0`, as in
  `Zeta5Irr.rhoA`; the sum over `1 ≤ j ≤ 16` is the sum over `Fin 16`.
* The weights `cⱼ` are nonnegative rationals, and enter the sum of measures as
  `ENNReal.ofReal cⱼ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3: the sixteen intervals.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory
open scoped ENNReal

/-- The rational arcsine measure `ρ = ∑_{j=1}^{16} cⱼ ω_{[aⱼ, bⱼ]}`. -/
@[zeta5irr "def_rho"]
noncomputable def rho : Measure ℝ :=
  ∑ j : Fin 16, ENNReal.ofReal (rhoC j) • arcsineMeasure (rhoA j) (rhoB j)

/-- The mass of a set under `ρ` is `∑ⱼ cⱼ ω_{[aⱼ, bⱼ]}(s)`. -/
lemma rho_apply (s : Set ℝ) :
    rho s = ∑ j : Fin 16, ENNReal.ofReal (rhoC j) * arcsineMeasure (rhoA j) (rhoB j) s := by
  simp [rho]

/-- The total mass of `ρ` is `∑ⱼ cⱼ`. -/
lemma rho_univ : rho Set.univ = ENNReal.ofReal (∑ j : Fin 16, (rhoC j : ℝ)) := by
  rw [rho_apply, ENNReal.ofReal_sum_of_nonneg fun j _ ↦ by exact_mod_cast rhoC_nonneg j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have := isProbabilityMeasure_arcsineMeasure (rhoA_lt_rhoB_real j)
  simp

/-- `ρ` is a finite measure. -/
instance isFiniteMeasure_rho : IsFiniteMeasure rho :=
  ⟨by rw [rho_univ]; exact ENNReal.ofReal_lt_top⟩

end Zeta5Irr
