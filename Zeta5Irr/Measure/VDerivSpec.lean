/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VDeriv
public import Zeta5Irr.Measure.VFormula

/-!
# The derivative of the field in the square-root variable

For `y > 0` the function `y ↦ V(y²)` is differentiable at `y`, with derivative
`W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))`. Near such a `y` the closed form of `V`
gives `V(y²) = log (1 + y²) - 6 α log (y² + α²) - 2 + 12 α + y W(y)`; differentiating,
the contributions of the logarithms cancel those of the arctangents, leaving `W(y)`.

## Main results

* `Zeta5Irr.hasDerivAt_externalField_sq`: for `y > 0`, `(V(y²))' = W(y)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5: the shape of the field.
-/

@[expose] public section

namespace Zeta5Irr

open Real Filter

/-- For `y > 0`, the external field in the square-root variable, `y ↦ V(y²)`, has derivative
`W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))` at `y`. -/
@[zeta5irr "lem_V_deriv"]
theorem hasDerivAt_externalField_sq {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => externalField (y ^ 2)) (fieldDeriv y) y := by
  set a : ℝ := (innerRatio : ℝ)
  have ha : 0 < a := by simp [a, innerRatio]
  let g : ℝ → ℝ := fun z => log (1 + z ^ 2) - 6 * a * log (z ^ 2 + a ^ 2) - 2 + 12 * a +
    z * fieldDeriv z
  have hg : (fun z : ℝ => externalField (z ^ 2)) =ᶠ[nhds y] g := by
    filter_upwards [lt_mem_nhds hy] with z hz
    rw [externalField_eq (by positivity), sqrt_sq hz.le]
    simp only [g, fieldDeriv, a]
    ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ hg
  have hy0 : y ≠ 0 := hy.ne'
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have h1 : HasDerivAt (fun z : ℝ => log (1 + z ^ 2)) ((2 * y) / (1 + y ^ 2)) y :=
    (hsq.const_add 1).log (by positivity)
  have h2 : HasDerivAt (fun z : ℝ => log (z ^ 2 + a ^ 2)) ((2 * y) / (y ^ 2 + a ^ 2)) y :=
    (hsq.add_const _).log (by positivity)
  have h3 := (hasDerivAt_id y).mul (hasDerivAt_fieldDeriv hy0)
  have := ((((h1.sub (h2.const_mul (6 * a))).sub_const 2).add_const (12 * a)).add h3)
  refine this.congr_deriv ?_
  simp only [id, one_mul, a]
  have hy2 : 0 < y ^ 2 := by positivity
  have hb : 0 < (innerRatio : ℝ) ^ 2 + y ^ 2 := by positivity
  have hc : 0 < y ^ 2 + (innerRatio : ℝ) ^ 2 := by positivity
  field_simp
  ring

end Zeta5Irr
