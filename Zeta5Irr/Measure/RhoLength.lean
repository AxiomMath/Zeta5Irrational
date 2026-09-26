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
# The sixteen intervals are longer than `1 / 225`

For every `1 ≤ j ≤ 16`, the interval `[aⱼ, bⱼ]` of the rational arcsine measure has length
`bⱼ - aⱼ > 1 / 225`. Multiplying by `10¹²`, this is the statement that
`225 · (10¹² bⱼ - 10¹² aⱼ) > 10¹²` for the integers of the table. The differences increase
with `j`, and already the first one satisfies `225 · 5085947445 = 1144338175125 > 10¹²`.

## Main results

* `Zeta5Irr.rhoNum_length`: the integer form `10¹² < 225 · (10¹² bⱼ - 10¹² aⱼ)`.
* `Zeta5Irr.rho_length`: `1 / 225 < bⱼ - aⱼ` for every row `j`.

## Implementation notes

Rows are indexed by `Fin 16` starting at `0`, as in the table of the rational arcsine
measure. The integer inequality is checked row by row by evaluation.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

/-- The integer form of the length bound: `10¹² < 225 · (10¹² bⱼ - 10¹² aⱼ)`, where the
difference is taken in `ℤ`. -/
theorem rhoNum_length (j : Fin 16) :
    (10 : ℤ) ^ 12 < 225 * ((rhoBNum j : ℤ) - rhoANum j) := by
  fin_cases j <;> simp [rhoANum, rhoBNum]

/-- Each of the sixteen intervals `[aⱼ, bⱼ]` of the rational arcsine measure has length
greater than `1 / 225`. -/
@[zeta5irr "lem_rho_length"]
theorem rho_length (j : Fin 16) : (1 : ℚ) / 225 < rhoB j - rhoA j := by
  have h : ((10 : ℤ) ^ 12 : ℚ) < ((225 * ((rhoBNum j : ℤ) - rhoANum j) : ℤ) : ℚ) := by
    exact_mod_cast rhoNum_length j
  push_cast at h
  rw [rhoA_eq, rhoB_eq, ← sub_div, div_lt_div_iff₀ (by norm_num) (by norm_num)]
  linarith

end Zeta5Irr
