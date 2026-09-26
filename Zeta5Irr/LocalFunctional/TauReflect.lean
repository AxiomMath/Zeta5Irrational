/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauX
public import Zeta5Irr.LocalFunctional.TauLReflect
public import Zeta5Irr.LocalFunctional.ReflectIndexReflect

/-!
# The reflection identity for `τ_X`

For a finite set `R ⊆ ℤ` write `R^* = {-1 - r : r ∈ R}`. For every `A ∈ ℚ[x]`,
`τ_X(A(-1 - x); R^*) = (-1)^{#R+1} τ_X(A; R)`.

Write `A = P E_R + B` with `deg B < #R`. Substituting `x ↦ -1 - x` and using
`E_R(-1 - x) = (-1)^{#R} E_{R^*}(x)` gives the decomposition
`A(-1 - x) = ((-1)^{#R} P(-1 - x)) E_{R^*} + B(-1 - x)` with `deg B(-1 - x) = deg B < #R^*`.
The polynomial part contributes `(-1)^{#R} τ(P(-1 - x)) = (-1)^{#R+1} τ(P)`, because `τ` is odd
under the reflection. At the pole `-1 - r ∈ R^*` the residue is
`A(r) / E_{R^*}'(-1 - r) = (-1)^{#R+1} A(r) / E_R'(r)`, and `d(-1 - r) = d(r)`.

## Main results

* `Zeta5Irr.tauX_image_neg_one_sub_comp`: the reflection identity above.
* `Zeta5Irr.intPoleProduct_image_neg_one_sub`: `E_{R^*}(x) = (-1)^{#R} E_R(-1 - x)`.
* `Zeta5Irr.tau_comp_neg_one_sub_X`: `τ(P(-1 - x)) = -τ(P)`.

## Implementation notes

The source proves the identity through the partial-fraction form of the remainder and the
witnessed decomposition of `τ_X`. Here the remainder `B` is carried along directly: `τ_X` may be
computed from any decomposition `A = P E_R + B` with `deg B < #R`, and the residues
`A(r) / E_R'(r)` are read off from `A` itself, so the partial-fraction coefficients never need
to be named. The sign `(-1)^{#R+1}` acts on `ℚ[X]` by scalar multiplication.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.2 (The reflection and difference identities).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C derivative eval)

/-- Reflecting the poles: `E_{R^*}(x) = (-1)^{#R} E_R(-1 - x)`, where
`R^* = {-1 - r : r ∈ R}`. -/
theorem intPoleProduct_image_neg_one_sub (S : Finset ℤ) (K : Type*) [CommRing K] :
    intPoleProduct (S.image (fun r ↦ -1 - r)) K =
      (-1) ^ S.card * (intPoleProduct S K).comp (-1 - X) := by
  rw [intPoleProduct, Finset.prod_image (fun a _ b _ h ↦ by simpa using h), intPoleProduct,
    Polynomial.prod_comp, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ ↦ ?_
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Int.cast_sub,
    Int.cast_neg, Int.cast_one, map_sub, map_neg, map_one]
  ring

/-- `τ` is odd under the reflection `x ↦ -1 - x`: `τ(P(-1 - x)) = -τ(P)`, since the third
derivative picks up a sign `(-1)^3` and `L` is reflection invariant. -/
theorem tau_comp_neg_one_sub_X (P : ℚ[X]) : tau (P.comp (-1 - X)) = -tau P := by
  have h : ∀ Q : ℚ[X], derivative (Q.comp (-1 - X)) = -(derivative Q).comp (-1 - X) := by
    intro Q
    rw [Polynomial.derivative_comp]
    simp
  rw [tau_apply, tau_apply]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, h,
    map_neg, neg_neg, bernoulliFunctional_comp_neg_one_sub_X]
  ring

/-- The residue denominators of the reflected poles: `E_{R^*}'(-1 - r) = (-1)^{#R+1} E_R'(r)`. -/
theorem eval_derivative_intPoleProduct_image_neg_one_sub (S : Finset ℤ) (K : Type*)
    [CommRing K] (r : ℤ) :
    (derivative (intPoleProduct (S.image (fun r ↦ -1 - r)) K)).eval ((-1 - r : ℤ) : K) =
      (-1) ^ (S.card + 1) * (derivative (intPoleProduct S K)).eval (r : K) := by
  rw [intPoleProduct_image_neg_one_sub S K, ← Polynomial.C_1, ← Polynomial.C_neg,
    ← Polynomial.C_pow, Polynomial.derivative_C_mul, Polynomial.derivative_comp]
  simp [pow_succ]

/-- The reflection identity for `τ_X`:
`τ_X(A(-1 - x); {-1 - r : r ∈ R}) = (-1)^{#R+1} τ_X(A; R)`. -/
@[zeta5irr "lem_tau_reflect"]
theorem tauX_image_neg_one_sub_comp (R : Finset ℤ) (A : ℚ[X]) :
    tauX (R.image (fun r ↦ -1 - r)) (A.comp (-1 - X)) =
      (-1 : ℚ) ^ (R.card + 1) • tauX R A := by
  set E := intPoleProduct R ℚ
  have hσ : (-1 - X : ℚ[X]).degree = 1 := by
    rw [show (-1 - X : ℚ[X]) = -(X + C 1) by simp; ring, Polynomial.degree_neg,
      Polynomial.degree_X_add_C]
  have hinj : Set.InjOn (fun r : ℤ ↦ -1 - r) R := fun a _ b _ h ↦ by simpa using h
  have hdecomp : A.comp (-1 - X) =
      ((-1) ^ R.card * (A /ₘ E).comp (-1 - X)) * intPoleProduct (R.image (fun r ↦ -1 - r)) ℚ +
        (A %ₘ E).comp (-1 - X) := by
    nth_rw 1 [← Polynomial.modByMonic_add_div A E]
    rw [intPoleProduct_image_neg_one_sub, Polynomial.add_comp, Polynomial.mul_comp]
    have : ((-1 : ℚ[X]) ^ R.card) * (-1) ^ R.card = 1 := by
      rw [← mul_pow]
      simp
    linear_combination (-(A /ₘ E).comp (-1 - X) * E.comp (-1 - X)) * this
  have hdeg : ((A %ₘ E).comp (-1 - X)).degree < (R.image (fun r ↦ -1 - r)).card := by
    rw [Finset.card_image_of_injOn hinj, Polynomial.degree_comp (by rw [hσ]; exact zero_lt_one), hσ,
      mul_one, ← degree_intPoleProduct R ℚ]
    exact Polynomial.degree_modByMonic_lt A (monic_intPoleProduct R ℚ)
  rw [tauX_eq_of_eq_add hdecomp hdeg, Finset.sum_image fun a ha b hb h ↦ hinj ha hb h, tauX,
    Polynomial.smul_eq_C_mul, mul_add, Finset.mul_sum]
  congr 1
  · rw [show ((-1 : ℚ[X]) ^ R.card * (A /ₘ E).comp (-1 - X)) =
        (-1 : ℚ) ^ R.card • (A /ₘ E).comp (-1 - X) by
          rw [Polynomial.smul_eq_C_mul]; simp, map_smul, tau_comp_neg_one_sub_X, ← map_mul]
    congr 1
    simp only [smul_eq_mul, pow_succ]
    ring
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hev : (A.comp (-1 - X)).eval ((-1 - r : ℤ) : ℚ) = A.eval (r : ℚ) := by
    simp [Polynomial.eval_comp]
  have hs : ((-1 : ℚ) ^ (R.card + 1))⁻¹ = (-1) ^ (R.card + 1) := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [reflectIndex_neg_one_sub, eval_derivative_intPoleProduct_image_neg_one_sub R ℚ, hev,
    ← mul_assoc, ← map_mul, div_mul_eq_div_div_swap, div_eq_mul_inv _ ((-1 : ℚ) ^ _), hs,
    mul_comm (eval _ A / _)]

end Zeta5Irr
