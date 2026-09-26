/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Simple partial fractions over the pole product

Let `S` be a finite set of natural numbers and `D_S(t) = ∏_{j ∈ S} (t + j ^ 2)` the pole
product. Over a field of characteristic zero the roots `-j ^ 2`, `j ∈ S`, of `D_S` are
distinct, so every polynomial `B` of degree less than `#S` is recovered from its values at
them by Lagrange interpolation:
`B = ∑_{j ∈ S} B(-j ^ 2) / D_S'(-j ^ 2) · D_{S \ {j}}`.
Dividing by `D_S` gives the decomposition of `B / D_S` into simple fractions,
`B(y ^ 2) / D_S(y ^ 2) = ∑_{j ∈ S} B(-j ^ 2) / D_S'(-j ^ 2) · 1 / (y ^ 2 + j ^ 2)`.

## Main results

* `Zeta5Irr.eval_poleProduct_erase_ne_zero`: this value is nonzero in characteristic zero.
* `Zeta5Irr.eq_sum_poleProduct_erase`: the interpolation identity for `B`.
* `Zeta5Irr.aeval_div_poleProduct_eq_sum`: the partial fraction decomposition of `B / D_S`
  at any point of an algebra over the coefficient field where `D_S` does not vanish.
* `Zeta5Irr.aeval_sq_div_poleProduct_eq_sum`: the decomposition at `t = y ^ 2`, `y` real.

## Implementation notes

The source takes `S ⊆ ℤ_{>0}` finite and nonempty. Here `S` is a `Finset ℕ`; the
interpolation identity needs neither positivity nor nonemptiness (for `S = ∅` the hypothesis
`deg B < 0` forces `B = 0`), and positivity `0 ∉ S` is used only to ensure
`y ^ 2 + j ^ 2 ≠ 0` at every real `y`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- In characteristic zero,
`D_{S \ {j}}(-j ^ 2) = ∏_{k ∈ S, k ≠ j} (k ^ 2 - j ^ 2) ≠ 0`. -/
theorem eval_poleProduct_erase_ne_zero (S : Finset ℕ) (j : ℕ) :
    (poleProduct (S.erase j) K).eval (-(j : K) ^ 2) ≠ 0 := by
  rw [eval_poleProduct, prod_ne_zero_iff]
  intro k hk
  have hkj : k ≠ j := (mem_erase.1 hk).1
  intro h
  have : ((k : K) - j) * ((k : K) + j) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact hkj (by exact_mod_cast sub_eq_zero.1 h')
  · have : ((k + j : ℕ) : K) = 0 := by push_cast; exact h'
    have : k + j = 0 := by exact_mod_cast this
    omega

/-- The derivative of the pole product does not vanish at its roots. -/
theorem eval_derivative_poleProduct_ne_zero {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) :
    (derivative (poleProduct S K)).eval (-(j : K) ^ 2) ≠ 0 := by
  rw [eval_derivative_poleProduct S hj]
  exact eval_poleProduct_erase_ne_zero S j

/-- Lagrange interpolation at the roots of the pole product: a polynomial `B` of degree less
than `#S` equals `∑_{j ∈ S} B(-j ^ 2) / D_S'(-j ^ 2) · D_{S \ {j}}`. -/
theorem eq_sum_poleProduct_erase (S : Finset ℕ) {B : K[X]} (hB : B.degree < #S) :
    B = ∑ j ∈ S,
      C (B.eval (-(j : K) ^ 2) / (derivative (poleProduct S K)).eval (-(j : K) ^ 2)) *
        poleProduct (S.erase j) K := by
  classical
  have hinj : Set.InjOn (fun j : ℕ ↦ -(j : K) ^ 2) S := by
    intro a _ b _ h
    by_contra hab
    have := eval_poleProduct_erase_ne_zero (K := K) {a, b} b
    rw [eval_poleProduct] at this
    apply this
    refine prod_eq_zero (i := a) (mem_erase.2 ⟨hab, mem_insert_self _ _⟩) ?_
    simp only at h
    linear_combination -h
  refine eq_of_degree_sub_lt_of_eval_finset_eq (S.image fun j : ℕ ↦ -(j : K) ^ 2) ?_ ?_
  · rw [card_image_of_injOn hinj]
    refine (degree_sub_le _ _).trans_lt (max_lt hB ?_)
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
    intro j hj
    refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_poleProduct, card_erase_of_mem hj]
    refine (add_le_add_left (degree_C_le (R := K)) _).trans_lt ?_
    have : 0 < #S := card_pos.2 ⟨j, hj⟩
    rw [zero_add]
    exact_mod_cast Nat.sub_lt this one_pos
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro j hj
    rw [eval_finsetSum, sum_eq_single_of_mem j hj, eval_mul, eval_C,
      eval_derivative_poleProduct S hj, div_mul_cancel₀ _ (eval_poleProduct_erase_ne_zero S j)]
    intro k hk hkj
    rw [eval_mul, eval_neg_sq_poleProduct_of_mem (mem_erase.2 ⟨Ne.symm hkj, hj⟩), mul_zero]

variable {L : Type*} [Field L] [Algebra K L]

/-- Partial fractions over the pole product: if `deg B < #S` and `D_S(x) ≠ 0`, then
`B(x) / D_S(x) = ∑_{j ∈ S} B(-j ^ 2) / D_S'(-j ^ 2) · 1 / (x + j ^ 2)`. -/
theorem aeval_div_poleProduct_eq_sum (S : Finset ℕ) {B : K[X]} (hB : B.degree < #S) {x : L}
    (hx : aeval x (poleProduct S K) ≠ 0) :
    aeval x B / aeval x (poleProduct S K) =
      ∑ j ∈ S, algebraMap K L
        (B.eval (-(j : K) ^ 2) / (derivative (poleProduct S K)).eval (-(j : K) ^ 2)) *
          (1 / (x + (j : L) ^ 2)) := by
  conv_lhs => rw [eq_sum_poleProduct_erase S hB]
  rw [map_sum, sum_div]
  refine sum_congr rfl fun j hj ↦ ?_
  have hD : aeval x (poleProduct S K) =
      (x + (j : L) ^ 2) * aeval x (poleProduct (S.erase j) K) := by
    conv_lhs => rw [← insert_erase hj]
    rw [poleProduct_insert K (S.notMem_erase j), map_mul]
    simp
  rw [hD] at hx ⊢
  rw [map_mul, aeval_C, mul_div_assoc,
    div_mul_cancel_right₀ (right_ne_zero_of_mul hx), one_div]

end Field

/-- **Simple partial fractions.** For a finite `S ⊆ ℤ_{>0}` and `B ∈ ℚ[t]` with
`deg B < #S`, for every real `y`,
`B(y ^ 2) / D_S(y ^ 2) = ∑_{j ∈ S} B(-j ^ 2) / D_S'(-j ^ 2) · 1 / (y ^ 2 + j ^ 2)`. -/
@[zeta5irr "lem_w_partial_fractions"]
theorem aeval_sq_div_poleProduct_eq_sum {S : Finset ℕ} (hS : 0 ∉ S) {B : ℚ[X]}
    (hB : B.degree < #S) (y : ℝ) :
    aeval (y ^ 2) B / aeval (y ^ 2) (poleProduct S ℚ) =
      ∑ j ∈ S,
        ((B.eval (-(j : ℚ) ^ 2) / (derivative (poleProduct S ℚ)).eval (-(j : ℚ) ^ 2) : ℚ) : ℝ) *
          (1 / (y ^ 2 + (j : ℝ) ^ 2)) := by
  refine aeval_div_poleProduct_eq_sum S hB ?_
  rw [aeval_poleProduct]
  refine prod_ne_zero_iff.2 fun j hj ↦ ?_
  have : j ≠ 0 := fun h ↦ hS (h ▸ hj)
  positivity

end Zeta5Irr
