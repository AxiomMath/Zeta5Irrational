/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The rank-defect correction `d_rk`

The outer limiting function carries a correction for the rank defect of the outer block,
supported on the open interval `(1/3, 1/2)`:
`d_rk(y) = (1 + 4 α - 3 y - (1 + α - 3 y)₊)₊ · 𝟙_{(1/3, 1/2)}(y)`,
where `α = 3/40` is the inner ratio and `t₊ = max t 0` is the positive part.

Unwinding the two positive parts, `d_rk` is piecewise affine: it equals `3 α` on
`(1/3, (1 + α)/3]`, equals `1 + 4 α - 3 y` on `[(1 + α)/3, (1 + 4 α)/3]`, and vanishes
from `(1 + 4 α)/3 = 13/30` on (and outside `(1/3, 1/2)`).

## Main definitions

* `Zeta5Irr.rankDefect`: the function `d_rk`.

## Main results

* `Zeta5Irr.rankDefect_of_mem`, `Zeta5Irr.rankDefect_of_not_mem`: the two branches of the
  indicator.
* `Zeta5Irr.rankDefect_eq_indicator`: `d_rk` as a `Set.indicator` of `Set.Ioo (1/3) (1/2)`.
* `Zeta5Irr.rankDefect_nonneg`: `0 ≤ d_rk(y)`.
* `Zeta5Irr.rankDefect_of_le`, `Zeta5Irr.rankDefect_of_ge_of_le`,
  `Zeta5Irr.rankDefect_of_ge`: the three affine pieces on `(1/3, 1/2)`.

## Implementation notes

* The source defines `d_rk` for `y ≥ 1/3`. The formula makes sense for every real `y`
  (and gives `0` for `y ≤ 1/3`), so `d_rk` is defined on all of `ℝ`.
* The indicator is written as an `if` rather than `Set.indicator`, so that the branch can be
  decided by `simp` or `norm_num` on concrete subintervals; `rankDefect_eq_indicator`
  gives the `Set.indicator` form.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.2 (The outer limiting function).
-/

@[expose] public section

namespace Zeta5Irr

/-- The rank-defect correction
`d_rk(y) = (1 + 4 α - 3 y - (1 + α - 3 y)₊)₊ · 𝟙_{(1/3, 1/2)}(y)`, where `α = 3/40` is the
inner ratio. The source restricts to `y ≥ 1/3`; the formula is used for all real `y`. -/
@[zeta5irr "def_drank"]
noncomputable def rankDefect (y : ℝ) : ℝ :=
  if 1 / 3 < y ∧ y < 1 / 2 then
    (1 + 4 * (innerRatio : ℝ) - 3 * y - (1 + (innerRatio : ℝ) - 3 * y)⁺)⁺
  else 0

/-- On `(1/3, 1/2)`, `d_rk(y) = (1 + 4 α - 3 y - (1 + α - 3 y)₊)₊`. -/
theorem rankDefect_of_mem {y : ℝ} (h₁ : 1 / 3 < y) (h₂ : y < 1 / 2) :
    rankDefect y = (1 + 4 * (innerRatio : ℝ) - 3 * y - (1 + (innerRatio : ℝ) - 3 * y)⁺)⁺ :=
  ite_eq_left ⟨h₁, h₂⟩

/-- Outside `(1/3, 1/2)`, `d_rk(y) = 0`. -/
theorem rankDefect_of_not_mem {y : ℝ} (h : ¬(1 / 3 < y ∧ y < 1 / 2)) : rankDefect y = 0 :=
  ite_eq_right h

/-- For `y ≤ 1/3`, `d_rk(y) = 0`. -/
theorem rankDefect_of_le_one_third {y : ℝ} (h : y ≤ 1 / 3) : rankDefect y = 0 :=
  rankDefect_of_not_mem fun h' => (h.trans_lt h'.1).false

/-- For `y ≥ 1/2`, `d_rk(y) = 0`. -/
theorem rankDefect_of_one_half_le {y : ℝ} (h : 1 / 2 ≤ y) : rankDefect y = 0 :=
  rankDefect_of_not_mem fun h' => (h.trans_lt h'.2).false

/-- `d_rk` as the indicator of `(1/3, 1/2)` times the double positive part. -/
theorem rankDefect_eq_indicator :
    rankDefect = (Set.Ioo (1 / 3 : ℝ) (1 / 2)).indicator
      fun y => (1 + 4 * (innerRatio : ℝ) - 3 * y - (1 + (innerRatio : ℝ) - 3 * y)⁺)⁺ := by
  ext y
  simp only [rankDefect, Set.indicator, Set.mem_Ioo]

/-- The rank-defect correction is nonnegative: `0 ≤ d_rk(y)`. -/
theorem rankDefect_nonneg (y : ℝ) : 0 ≤ rankDefect y := by
  unfold rankDefect
  split_ifs
  exacts [posPart_nonneg _, le_rfl]

/-- On `(1/3, (1 + α)/3]`, `d_rk(y) = 3 α`. -/
theorem rankDefect_of_le {y : ℝ} (h₁ : 1 / 3 < y) (h₂ : y ≤ (1 + (innerRatio : ℝ)) / 3) :
    rankDefect y = 3 * (innerRatio : ℝ) := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hin : (1 + (innerRatio : ℝ) - 3 * y)⁺ = 1 + innerRatio - 3 * y :=
    posPart_eq_self.2 (by linarith)
  rw [rankDefect_of_mem h₁ (by rw [hα] at h₂; linarith), hin,
    posPart_eq_self.2 (by rw [hα]; linarith)]
  ring

/-- On `[(1 + α)/3, (1 + 4 α)/3]`, `d_rk(y) = 1 + 4 α - 3 y`. -/
theorem rankDefect_of_ge_of_le {y : ℝ} (h₁ : (1 + (innerRatio : ℝ)) / 3 ≤ y)
    (h₂ : y ≤ (1 + 4 * (innerRatio : ℝ)) / 3) :
    rankDefect y = 1 + 4 * (innerRatio : ℝ) - 3 * y := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hin : (1 + (innerRatio : ℝ) - 3 * y)⁺ = 0 := posPart_eq_zero.2 (by linarith)
  rw [rankDefect_of_mem (by rw [hα] at h₁; linarith) (by rw [hα] at h₂; linarith), hin,
    sub_zero, posPart_eq_self.2 (by linarith)]

/-- For `y ≥ (1 + 4 α)/3 = 13/30`, `d_rk(y) = 0`. -/
theorem rankDefect_of_ge {y : ℝ} (h : (1 + 4 * (innerRatio : ℝ)) / 3 ≤ y) :
    rankDefect y = 0 := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  by_cases hy : y < 1 / 2
  · have hin : (1 + (innerRatio : ℝ) - 3 * y)⁺ = 0 :=
      posPart_eq_zero.2 (by rw [hα] at h ⊢; linarith)
    rw [rankDefect_of_mem (by rw [hα] at h; linarith) hy, hin, sub_zero,
      posPart_eq_zero.2 (by linarith)]
  · exact rankDefect_of_one_half_le (not_lt.1 hy)

end Zeta5Irr
