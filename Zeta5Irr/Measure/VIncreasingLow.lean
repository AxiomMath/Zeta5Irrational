/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VDeriv
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

/-!
# `W` is increasing near the origin

Let `W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))` with `α = 3/40`. Its derivative is
`W'(y) = -2 / (1 + y²) + 12 α / (α² + y²)`, and clearing the positive denominators,
`W'(y) > 0` exactly when `y² (12 α - 2) > 2 α² - 12 α`. Since `12 α - 2 = -11/10 < 0` this is
`y² < 711/880`, which holds for `0 < y < 4/5` because `16/25 < 711/880`. Hence `W` is strictly
increasing on `(0, 4/5)`.

## Main results

* `Zeta5Irr.fieldDeriv_deriv_pos`: `W'(y) > 0` for `0 < y < 4/5`.
* `Zeta5Irr.strictMonoOn_fieldDeriv_Ioo`: `W` is strictly increasing on `(0, 4/5)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5 (The shape of the field).
-/

@[expose] public section

namespace Zeta5Irr

open Real Set

/-- The derivative of `W` is positive on `(0, 4/5)`:
`-2 / (1 + y²) + 12 α / (α² + y²) > 0` for `0 < y < 4/5`. -/
theorem fieldDeriv_deriv_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (4 / 5)) :
    0 < -2 / (1 + y ^ 2) + 12 * (innerRatio : ℝ) / ((innerRatio : ℝ) ^ 2 + y ^ 2) := by
  obtain ⟨h0, h1⟩ := hy
  have hy2 : y ^ 2 < 16 / 25 := by nlinarith
  rw [show (innerRatio : ℝ) = 3 / 40 by norm_num [innerRatio]]
  have hd1 : 0 < 1 + y ^ 2 := by positivity
  have hd2 : 0 < (3 / 40 : ℝ) ^ 2 + y ^ 2 := by positivity
  rw [div_add_div _ _ hd1.ne' hd2.ne']
  exact div_pos (by nlinarith) (mul_pos hd1 hd2)

/-- **`W` is increasing near the origin.** The function
`W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))` is strictly increasing on `(0, 4/5)`. -/
@[zeta5irr "lem_V_increasing_low"]
theorem strictMonoOn_fieldDeriv_Ioo : StrictMonoOn fieldDeriv (Ioo (0 : ℝ) (4 / 5)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (continuousOn_fieldDeriv.mono Ioo_subset_Ioi_self) ?_
  rw [interior_Ioo]
  exact fun y hy => (hasDerivAt_fieldDeriv hy.1.ne').deriv ▸ fieldDeriv_deriv_pos hy

end Zeta5Irr
