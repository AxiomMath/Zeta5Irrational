/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Measure.Rho

/-!
# The total mass of `ρ`

The rational arcsine measure `ρ = ∑_{j=1}^{16} cⱼ ω_{[aⱼ, bⱼ]}` has total mass `λ = 37/40`.
Each interval `[aⱼ, bⱼ]` is nondegenerate, so each `ω_{[aⱼ, bⱼ]}` is a probability measure
and `ρ(ℝ) = ∑ⱼ cⱼ`; the sixteen integers `10¹² cⱼ` of the table sum to `925000000000`, so
`∑ⱼ cⱼ = 925000000000 / 10¹² = 37/40`.

## Main results

* `Zeta5Irr.sum_rhoC`: the weights of the table sum to `λ`: `∑ⱼ cⱼ = λ`.
* `Zeta5Irr.rho_univ_eq_orderRatio`: the total mass of `ρ` is `λ`: `ρ(ℝ) = λ`.
* `Zeta5Irr.rho_real_univ`: the same statement for the real-valued mass `ρ.real ℝ`.

## Implementation notes

* The measure `ρ` takes values in `ℝ≥0∞`, so the statement `ρ(ℝ) = λ` reads
  `ρ univ = ENNReal.ofReal λ`, with `λ` the rational `Zeta5Irr.orderRatio` cast to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- The integer column `10¹² cⱼ` of the table sums to `925000000000`. -/
theorem sum_rhoCNum : ∑ j : Fin 16, rhoCNum j = 925000000000 := by
  simp [Fin.sum_univ_succ, rhoCNum]

/-- The sixteen weights of the table sum to `λ = 37/40`. -/
theorem sum_rhoC : ∑ j : Fin 16, rhoC j = orderRatio := by
  simp_rw [rhoC, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_rhoCNum, orderRatio]
  norm_num

/-- The total mass of `ρ` is `λ = 37/40`. -/
@[zeta5irr "lem_rho_mass"]
theorem rho_univ_eq_orderRatio : rho Set.univ = ENNReal.ofReal (orderRatio : ℝ) := by
  rw [rho_univ, ← sum_rhoC, Rat.cast_sum]

/-- The real-valued total mass of `ρ` is `λ = 37/40`. -/
theorem rho_real_univ : rho.real Set.univ = orderRatio := by
  rw [measureReal_def, rho_univ_eq_orderRatio, ENNReal.toReal_ofReal (by norm_num [orderRatio])]

end Zeta5Irr
