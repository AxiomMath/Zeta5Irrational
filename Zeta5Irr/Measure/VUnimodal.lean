/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VIncreasingLow
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `W` changes sign at most once

Let `W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))` with `α = 3/40`. For `0 < y₁ < y₂`,
if `W(y₁) ≥ 0` then `W(y₂) > 0`.

If `y₂ ≥ 4/5`, then `arctan (1 / y₂) > 0` and `arctan (α / y₂) ≤ α / y₂`, so
`W(y₂) > 2 (π - 6 α / y₂) ≥ 2 (π - 9/16) > 0` since `6 α = 9/20` and `π > 3`.
If `y₂ < 4/5`, then `W` is strictly increasing on `(0, 4/5)`, so `W(y₂) > W(y₁) ≥ 0`.

## Main results

* `Zeta5Irr.fieldDeriv_pos_of_le`: `W(y) > 0` for `y ≥ 4/5`.
* `Zeta5Irr.fieldDeriv_pos_of_nonneg_of_lt`: for `0 < y₁ < y₂` with `W(y₁) ≥ 0`, `W(y₂) > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5 (The shape of the field).
-/

@[expose] public section

namespace Zeta5Irr

open Real Set

/-- `W` is positive on `[4/5, ∞)`. -/
theorem fieldDeriv_pos_of_le {y : ℝ} (hy : 4 / 5 ≤ y) : 0 < fieldDeriv y := by
  have hy0 : 0 < y := by linarith
  have hA : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have h1 : 0 < arctan (1 / y) := by
    rw [← arctan_zero]; exact arctan_strictMono (by positivity)
  have h2 : arctan ((innerRatio : ℝ) / y) ≤ (innerRatio : ℝ) / y :=
    arctan_le_self (by rw [hA]; positivity)
  have h3 : (innerRatio : ℝ) / y ≤ 3 / 32 := by
    rw [hA, div_le_iff₀ hy0]; linarith
  have := pi_gt_three
  unfold fieldDeriv
  linarith

/-- **`W` changes sign at most once.** For `0 < y₁ < y₂`, if `W(y₁) ≥ 0` then `W(y₂) > 0`. -/
@[zeta5irr "lem_V_unimodal"]
theorem fieldDeriv_pos_of_nonneg_of_lt {y₁ y₂ : ℝ} (h₀ : 0 < y₁) (h₁₂ : y₁ < y₂)
    (hW : 0 ≤ fieldDeriv y₁) : 0 < fieldDeriv y₂ := by
  rcases le_or_gt (4 / 5) y₂ with h | h
  · exact fieldDeriv_pos_of_le h
  · exact hW.trans_lt <| strictMonoOn_fieldDeriv_Ioo ⟨h₀, h₁₂.trans h⟩ ⟨h₀.trans h₁₂, h⟩ h₁₂

end Zeta5Irr
