/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The derivative of the field in the square-root variable

For `y > 0` put
`W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))`, where `α = 3/40` is the inner ratio.
This is the derivative of `y ↦ V(y²)`, the field `V` read in the square-root variable
`y = √t`; its shape (increasing near `0`, at most one sign change) governs the shape of `V`.

## Main definitions

* `Zeta5Irr.fieldDeriv`: the function `W`.

## Main results

* `Zeta5Irr.hasDerivAt_fieldDeriv`: for `y ≠ 0`,
  `W'(y) = -2 / (1 + y²) + 12 α / (α² + y²)`.

## Implementation notes

* The source defines `W` only for `y > 0`. Here it is a total function `ℝ → ℝ`, given by the
  same formula; with Mathlib's convention `1 / 0 = 0` its value at `0` is `2π`, and it is
  never used there. Hypotheses `0 < y` go on the lemmas that need them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5: the shape of the field.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The derivative of the field in the square-root variable,
`W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))` with `α = 3/40`. The source considers only
`y > 0`; the formula is used on all of `ℝ`. -/
@[zeta5irr "def_V_deriv"]
noncomputable def fieldDeriv (y : ℝ) : ℝ :=
  2 * (π + arctan (1 / y) - 6 * arctan ((innerRatio : ℝ) / y))

/-- The derivative of `W`: for `y ≠ 0`, `W'(y) = -2 / (1 + y²) + 12 α / (α² + y²)`. -/
theorem hasDerivAt_fieldDeriv {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt fieldDeriv
      (-2 / (1 + y ^ 2) + 12 * (innerRatio : ℝ) / ((innerRatio : ℝ) ^ 2 + y ^ 2)) y := by
  set a : ℝ := (innerRatio : ℝ)
  have h1 : HasDerivAt (fun y : ℝ => 1 / y) (-(y ^ 2)⁻¹) y := by
    simpa [one_div] using hasDerivAt_inv hy
  have h2 : HasDerivAt (fun y : ℝ => a / y) (a * -(y ^ 2)⁻¹) y := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hy).const_mul a
  refine ((((h1.arctan).const_add π).sub ((h2.arctan).const_mul 6)).const_mul 2).congr_deriv ?_
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have ha : 0 < a ^ 2 + y ^ 2 := by positivity
  field_simp
  ring

/-- `W` is differentiable at every `y ≠ 0`. -/
theorem differentiableAt_fieldDeriv {y : ℝ} (hy : y ≠ 0) : DifferentiableAt ℝ fieldDeriv y :=
  (hasDerivAt_fieldDeriv hy).differentiableAt

/-- `W` is continuous on `(0, ∞)`. -/
theorem continuousOn_fieldDeriv : ContinuousOn fieldDeriv (Set.Ioi 0) := fun _ hy =>
  (differentiableAt_fieldDeriv (ne_of_gt hy)).continuousAt.continuousWithinAt

end Zeta5Irr
