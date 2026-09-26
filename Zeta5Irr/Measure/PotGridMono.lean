/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotGridNotation
public import Zeta5Irr.Measure.RhoNested
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# The grid `A₀ < A₁ < ⋯ < A₃₅` is strictly increasing

The grid `A₀, …, A₃₅` partitioning `[0, 2]` is the list
`0, a₁₆, …, a₁, q₋, q₊, b₁, …, b₁₆, 2`. It is strictly increasing: the chains
`0 < a₁₆ < ⋯ < a₁` and `b₁ < ⋯ < b₁₆ < 2` are the nesting of the sixteen arcsine intervals,
and the three remaining links `a₁ < q₋ < q₊ < b₁` are comparisons of rationals, holding because
`3906748086 < 5920507700 < 5920507900 < 8992695531` after multiplication by `10¹²`.

## Main results

* `Zeta5Irr.strictMono_potGrid`: `A₀ < A₁ < ⋯ < A₃₅`.
* `Zeta5Irr.rhoA_zero_lt_externalFieldMinLower`, `Zeta5Irr.externalFieldMinUpper_lt_rhoB_zero`:
  the links `a₁ < q₋` and `q₊ < b₁`.
* `Zeta5Irr.potGrid_of_pos_of_le`, `Zeta5Irr.potGrid_of_le_of_le`: the values of `Aᵢ` for
  `1 ≤ i ≤ 16` and `19 ≤ i ≤ 34`, with the index as a variable.

## Implementation notes

* The chain `A₀ < A₁ < ⋯ < A₃₅` is stated as `StrictMono potGrid` on `Fin 36`, which is
  equivalent to it by `Fin.strictMono_iff_lt_succ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6 (The interval bound and the partition of `[0, 2]`).
-/

@[expose] public section

namespace Zeta5Irr

/-- The innermost left endpoint lies below the bracket of the minimum of the external field:
`a₁ < q₋`. -/
theorem rhoA_zero_lt_externalFieldMinLower : rhoA 0 < externalFieldMinLower := by
  rw [rhoA, externalFieldMinLower]; norm_num [rhoANum]

/-- The bracket of the minimum of the external field lies below the innermost right endpoint:
`q₊ < b₁`. -/
theorem externalFieldMinUpper_lt_rhoB_zero : externalFieldMinUpper < rhoB 0 := by
  rw [rhoB, externalFieldMinUpper]; norm_num [rhoBNum]

/-- For `1 ≤ i ≤ 16`, the grid point `Aᵢ` is the left endpoint `a₁₇₋ᵢ`, that is
`rhoA (16 - i)`. -/
theorem potGrid_of_pos_of_le {i : Fin 36} (h₀ : 0 < i.val) (h : i.val ≤ 16) :
    potGrid i = rhoA ⟨16 - i.val, by omega⟩ := by
  unfold potGrid
  split_ifs <;> first | omega | rfl

/-- For `19 ≤ i ≤ 34`, the grid point `Aᵢ` is the right endpoint `bᵢ₋₁₈`, that is
`rhoB (i - 19)`. -/
theorem potGrid_of_le_of_le {i : Fin 36} (h₀ : 19 ≤ i.val) (h : i.val ≤ 34) :
    potGrid i = rhoB ⟨i.val - 19, by omega⟩ := by
  unfold potGrid
  split_ifs <;> first | omega | rfl

/-- **The grid is strictly increasing**: `A₀ < A₁ < ⋯ < A₃₅`. -/
@[zeta5irr "lem_pot_grid_mono"]
theorem strictMono_potGrid : StrictMono potGrid := by
  obtain ⟨h0, hA, -, hB, h2⟩ := rhoA_nested
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hi := i.isLt
  have hc : (Fin.castSucc i).val = i.val := rfl
  have hs : (Fin.succ i).val = i.val + 1 := rfl
  obtain h | ⟨h, h'⟩ | h | h | h | ⟨h, h'⟩ | h : i.val = 0 ∨ (1 ≤ i.val ∧ i.val ≤ 15) ∨
      i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ (19 ≤ i.val ∧ i.val ≤ 33) ∨ i.val = 34 := by
    omega
  · -- `0 < a₁₆`
    rw [show Fin.castSucc i = 0 from Fin.ext (by rw [hc, h]; rfl), potGrid_zero,
      potGrid_of_pos_of_le (by omega) (by omega)]
    exact h0.trans_le (hA.antitone (Fin.le_def.2 (by simp [h])))
  · -- `a₁₇₋ᵢ < a₁₆₋ᵢ`
    rw [potGrid_of_pos_of_le (by omega) (by omega), potGrid_of_pos_of_le (by omega) (by omega)]
    exact hA (Fin.mk_lt_mk.2 (by omega))
  · -- `a₁ < q₋`
    rw [show Fin.succ i = 17 from Fin.ext (by rw [hs, h]; rfl), potGrid_seventeen,
      potGrid_of_pos_of_le (by omega) (by omega)]
    exact (hA.antitone (Fin.le_def.2 (by simp))).trans_lt rhoA_zero_lt_externalFieldMinLower
  · -- `q₋ < q₊`
    rw [show Fin.castSucc i = 17 from Fin.ext (by rw [hc, h]; rfl),
      show Fin.succ i = 18 from Fin.ext (by rw [hs, h]; rfl), potGrid_seventeen,
      potGrid_eighteen]
    exact externalFieldMinLower_lt_upper
  · -- `q₊ < b₁`
    rw [show Fin.castSucc i = 18 from Fin.ext (by rw [hc, h]; rfl), potGrid_eighteen,
      potGrid_of_le_of_le (by omega) (by omega)]
    exact externalFieldMinUpper_lt_rhoB_zero.trans_le (hB.monotone (Fin.le_def.2 (by simp)))
  · -- `bᵢ₋₁₈ < bᵢ₋₁₇`
    rw [potGrid_of_le_of_le (by omega) (by omega), potGrid_of_le_of_le (by omega) (by omega)]
    exact hB (Fin.mk_lt_mk.2 (by omega))
  · -- `b₁₆ < 2`
    rw [show Fin.succ i = 35 from Fin.ext (by rw [hs, h]; rfl), potGrid_thirtyFive,
      potGrid_of_le_of_le (by omega) (by omega)]
    exact (hB.monotone (Fin.le_def.2 (by simp; omega))).trans_lt h2

end Zeta5Irr
