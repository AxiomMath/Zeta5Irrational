/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoTableNotation
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star

/-!
# The sixteen intervals are nested

The sixteen intervals `[aⱼ, bⱼ]` of the rational arcsine measure are strictly nested inside
`(0, 2)`: `0 < a₁₆ < a₁₅ < ⋯ < a₁ < b₁ < b₂ < ⋯ < b₁₆ < 2`. Every inequality is a comparison
of integers of the table after multiplication by `10¹²`.

## Main results

* `Zeta5Irr.strictAnti_rhoA`: the left endpoints `aⱼ` are strictly decreasing in `j`.
* `Zeta5Irr.strictMono_rhoB`: the right endpoints `bⱼ` are strictly increasing in `j`.
* `Zeta5Irr.rhoA_lt_rhoB`, `Zeta5Irr.rhoA_lt_rhoB_real`: every interval `[aⱼ, bⱼ]` is
  nondegenerate.
* `Zeta5Irr.rhoA_nested`: the full chain
  `0 < a₁₆ < a₁₅ < ⋯ < a₁ < b₁ < b₂ < ⋯ < b₁₆ < 2`.

## Implementation notes

* The rows are indexed by `Fin 16` starting at `0`, so `a₁₆` is `rhoA 15` and `a₁` is
  `rhoA 0`. The two monotone chains of the source are stated as `StrictAnti rhoA` and
  `StrictMono rhoB`, joined by `a₁ < b₁` and bounded by `0 < a₁₆` and `b₁₆ < 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

/-- The integer column `10¹² aⱼ` is strictly decreasing. -/
theorem strictAnti_rhoANum : StrictAnti rhoANum := by
  rw [Fin.strictAnti_iff_succ_lt]
  decide

/-- The integer column `10¹² bⱼ` is strictly increasing. -/
theorem strictMono_rhoBNum : StrictMono rhoBNum := by
  rw [Fin.strictMono_iff_lt_succ]
  decide

/-- The left endpoints `aⱼ` of the sixteen intervals are strictly decreasing in `j`. -/
theorem strictAnti_rhoA : StrictAnti rhoA := fun i j hij => by
  rw [rhoA, rhoA]
  gcongr
  exact_mod_cast strictAnti_rhoANum hij

/-- The right endpoints `bⱼ` of the sixteen intervals are strictly increasing in `j`. -/
theorem strictMono_rhoB : StrictMono rhoB := fun i j hij => by
  rw [rhoB, rhoB]
  gcongr
  exact_mod_cast strictMono_rhoBNum hij

/-- The smallest left endpoint `a₁₆` is positive. -/
theorem rhoA_fifteen_pos : 0 < rhoA 15 := by
  rw [rhoA]; norm_num [rhoANum]

/-- Every interval `[aⱼ, bⱼ]` of the table is nondegenerate: `aⱼ < bⱼ`. -/
theorem rhoA_lt_rhoB (j : Fin 16) : rhoA j < rhoB j := by
  rw [rhoA, rhoB]
  gcongr
  exact_mod_cast (by fin_cases j <;> decide : rhoANum j < rhoBNum j)

/-- Every interval `[aⱼ, bⱼ]` of the table is nondegenerate, as real numbers. -/
theorem rhoA_lt_rhoB_real (j : Fin 16) : (rhoA j : ℝ) < rhoB j := by
  exact_mod_cast rhoA_lt_rhoB j

/-- The largest right endpoint `b₁₆` is less than `2`. -/
theorem rhoB_fifteen_lt_two : rhoB 15 < 2 := by
  rw [rhoB]; norm_num [rhoBNum]

/-- **The sixteen intervals are nested**:
`0 < a₁₆ < a₁₅ < ⋯ < a₁ < b₁ < b₂ < ⋯ < b₁₆ < 2`. -/
@[zeta5irr "lem_rho_nested"]
theorem rhoA_nested :
    0 < rhoA 15 ∧ StrictAnti rhoA ∧ rhoA 0 < rhoB 0 ∧ StrictMono rhoB ∧ rhoB 15 < 2 :=
  ⟨rhoA_fifteen_pos, strictAnti_rhoA, rhoA_lt_rhoB 0, strictMono_rhoB,
    rhoB_fifteen_lt_two⟩

end Zeta5Irr
