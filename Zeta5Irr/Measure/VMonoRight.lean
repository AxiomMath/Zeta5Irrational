/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VDerivSpec
public import Zeta5Irr.Measure.VUnimodal
public import Zeta5Irr.Measure.VMinLocate

/-!
# The external field is nondecreasing to the right of its minimum

For `q₊ ≤ s ≤ t` the external field satisfies `V(s) ≤ V(t)`. Indeed `W(√q₊) > 0`, so by the
unimodality of `W` it is positive on `[√q₊, ∞)`; since `W` is the derivative of `y ↦ V(y²)`,
this function is nondecreasing on `[√q₊, ∞)`, and taking square roots transfers this to `V`
on `[q₊, ∞)`.

## Main results

* `Zeta5Irr.monotoneOn_externalField_sq`: `y ↦ V(y²)` is monotone on `[√q₊, ∞)`.
* `Zeta5Irr.monotoneOn_externalField`: `V` is monotone on `[q₊, ∞)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5: the shape of the field.
-/

@[expose] public section

namespace Zeta5Irr

open Real Set

/-- `W` is positive on `[√q₊, ∞)`. -/
theorem fieldDeriv_pos_of_sqrt_externalFieldMinUpper_le {y : ℝ}
    (hy : √(externalFieldMinUpper : ℝ) ≤ y) : 0 < fieldDeriv y := by
  rcases hy.eq_or_lt with rfl | hlt
  · exact fieldDeriv_sqrt_externalFieldMinUpper_pos
  · exact fieldDeriv_pos_of_nonneg_of_lt
      (Real.sqrt_pos.2 (by exact_mod_cast externalFieldMinUpper_pos)) hlt
      fieldDeriv_sqrt_externalFieldMinUpper_pos.le

/-- The external field in the square-root variable, `y ↦ V(y²)`, is monotone on `[√q₊, ∞)`. -/
theorem monotoneOn_externalField_sq :
    MonotoneOn (fun y : ℝ => externalField (y ^ 2)) (Ici √(externalFieldMinUpper : ℝ)) := by
  have h0 : 0 < √(externalFieldMinUpper : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast externalFieldMinUpper_pos)
  have hd : ∀ y ∈ Ici √(externalFieldMinUpper : ℝ),
      HasDerivAt (fun y : ℝ => externalField (y ^ 2)) (fieldDeriv y) y :=
    fun y hy => hasDerivAt_externalField_sq (h0.trans_le hy)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => (fieldDeriv_pos_of_sqrt_externalFieldMinUpper_le (interior_subset hy)).le)

/-- **The external field is nondecreasing to the right of its minimum.** For `q₊ ≤ s ≤ t`,
`V(s) ≤ V(t)`. -/
@[zeta5irr "lem_V_mono_right"]
theorem monotoneOn_externalField :
    MonotoneOn externalField (Ici (externalFieldMinUpper : ℝ)) := by
  intro s hs t ht hst
  have hq : (0 : ℝ) ≤ externalFieldMinUpper := by exact_mod_cast externalFieldMinUpper_pos.le
  have hs0 : 0 ≤ s := hq.trans hs
  have ht0 : 0 ≤ t := hq.trans ht
  have h := monotoneOn_externalField_sq (Real.sqrt_le_sqrt (mem_Ici.1 hs))
    (Real.sqrt_le_sqrt (mem_Ici.1 ht)) (Real.sqrt_le_sqrt hst)
  simpa only [Real.sq_sqrt hs0, Real.sq_sqrt ht0] using h

end Zeta5Irr
