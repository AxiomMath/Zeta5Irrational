/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Kernel
public import Zeta5Irr.DegreePositivity.KernelPrimitiveDiv
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The kernel as a fourth derivative

For real `b ≠ 0` the kernel `Ψ_b` is, up to the factor `24 b⁴`, the fourth derivative of
`y ↦ y ^ 5 / (y ^ 2 + b ^ 2)`:
`(d/dy)⁴ (y ^ 5 / (y ^ 2 + b ^ 2)) = 24 b⁴ Ψ_b(y)`.

Write `D = y ^ 2 + b ^ 2`. By polynomial division,
`y ^ 5 / D = y ^ 3 - b ^ 2 y + b ^ 4 u(y)` with `u(y) = y / D`, and the successive
derivatives of `u` are
`u' = (b ^ 2 - y ^ 2) / D ^ 2`, `u'' = (2 y ^ 3 - 6 b ^ 2 y) / D ^ 3`,
`u''' = (-6 y ^ 4 + 36 b ^ 2 y ^ 2 - 6 b ^ 4) / D ^ 4` and
`u'''' = (24 y ^ 5 - 240 b ^ 2 y ^ 3 + 120 b ^ 4 y) / D ^ 5 = 24 Ψ_b(y)`,
while the fourth derivative of the cubic vanishes.

## Main results

* `Zeta5Irr.iteratedDeriv_four_pow_five_div_sq_add_sq`: the identity, for `b ≠ 0`.
* `Zeta5Irr.iteratedDeriv_four_pow_five_div_sq_add_sq_of_pos`: the source's form, for `b > 0`.

## Implementation notes

The source assumes `b > 0`; only `b ≠ 0` is used, since it makes `y ^ 2 + b ^ 2` nonzero on
all of `ℝ`, so the main statement is made under that hypothesis.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `b ≠ 0`, `(d/dy)⁴ (y ^ 5 / (y ^ 2 + b ^ 2)) = 24 b⁴ Ψ_b(y)`. -/
theorem iteratedDeriv_four_pow_five_div_sq_add_sq {b : ℝ} (hb : b ≠ 0) :
    iteratedDeriv 4 (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) =
      fun y => 24 * b ^ 4 * weightKernel b y := by
  have hD : ∀ y : ℝ, y ^ 2 + b ^ 2 ≠ 0 := fun y => by positivity
  have hDd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ 2 + b ^ 2) (2 * y) y := fun y => by
    simpa using (hasDerivAt_pow 2 y).add_const (b ^ 2)
  have hdiv : (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) =
      fun y => y ^ 3 - b ^ 2 * y + b ^ 4 * (y / (y ^ 2 + b ^ 2)) := by
    funext y
    rw [pow_five_div_sq_add_sq (hD y), mul_div_assoc]
  have h0 : deriv (fun y : ℝ => y ^ 3 - b ^ 2 * y + b ^ 4 * (y / (y ^ 2 + b ^ 2))) =
      fun y => 3 * y ^ 2 - b ^ 2 + b ^ 4 * ((b ^ 2 - y ^ 2) / (y ^ 2 + b ^ 2) ^ 2) := by
    funext y
    have := ((hasDerivAt_pow 3 y).sub ((hasDerivAt_id y).const_mul (b ^ 2))).add
      (((hasDerivAt_id y).div (hDd y) (hD y)).const_mul (b ^ 4))
    refine this.deriv.trans ?_
    simp only [id]
    field_simp
    ring
  have h1 : deriv (fun y : ℝ =>
      3 * y ^ 2 - b ^ 2 + b ^ 4 * ((b ^ 2 - y ^ 2) / (y ^ 2 + b ^ 2) ^ 2)) =
      fun y => 6 * y + b ^ 4 * ((2 * y ^ 3 - 6 * b ^ 2 * y) / (y ^ 2 + b ^ 2) ^ 3) := by
    funext y
    have := ((((hasDerivAt_pow 2 y).const_mul 3).sub_const (b ^ 2)).add
      ((((hasDerivAt_pow 2 y).const_sub (b ^ 2)).div ((hDd y).pow 2)
        (pow_ne_zero 2 (hD y))).const_mul (b ^ 4)))
    refine this.deriv.trans ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  have h2 : deriv (fun y : ℝ =>
      6 * y + b ^ 4 * ((2 * y ^ 3 - 6 * b ^ 2 * y) / (y ^ 2 + b ^ 2) ^ 3)) =
      fun y => 6 + b ^ 4 *
        ((-6 * y ^ 4 + 36 * b ^ 2 * y ^ 2 - 6 * b ^ 4) / (y ^ 2 + b ^ 2) ^ 4) := by
    funext y
    have := (((hasDerivAt_id y).const_mul 6).add
      (((((hasDerivAt_pow 3 y).const_mul 2).sub ((hasDerivAt_id y).const_mul (6 * b ^ 2))).div
        ((hDd y).pow 3) (pow_ne_zero 3 (hD y))).const_mul (b ^ 4)))
    refine this.deriv.trans ?_
    simp only [Pi.sub_apply, Pi.pow_apply, id]
    field_simp
    ring
  have h3 : deriv (fun y : ℝ =>
      6 + b ^ 4 * ((-6 * y ^ 4 + 36 * b ^ 2 * y ^ 2 - 6 * b ^ 4) / (y ^ 2 + b ^ 2) ^ 4)) =
      fun y => 24 * b ^ 4 * weightKernel b y := by
    funext y
    have := (((((((hasDerivAt_pow 4 y).const_mul (-6)).add
      ((hasDerivAt_pow 2 y).const_mul (36 * b ^ 2))).sub_const (6 * b ^ 4)).div
        ((hDd y).pow 4) (pow_ne_zero 4 (hD y))).const_mul (b ^ 4)).const_add 6)
    refine this.deriv.trans ?_
    simp only [Pi.add_apply, Pi.pow_apply]
    rw [weightKernel_def]
    field_simp
    ring
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_one,
    hdiv, h0, h1, h2, h3]

/-- **The kernel as a fourth derivative.** For real `b > 0` and every real `y`,
`(d/dy)⁴ (y ^ 5 / (y ^ 2 + b ^ 2)) = 24 b⁴ Ψ_b(y)`. -/
@[zeta5irr "lem_w_ker_deriv"]
theorem iteratedDeriv_four_pow_five_div_sq_add_sq_of_pos {b : ℝ} (hb : 0 < b) (y : ℝ) :
    iteratedDeriv 4 (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y = 24 * b ^ 4 * weightKernel b y :=
  congrFun (iteratedDeriv_four_pow_five_div_sq_add_sq hb.ne') y

end Zeta5Irr
