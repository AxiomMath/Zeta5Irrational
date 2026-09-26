/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.ENatToNat

/-!
# The sign of the determinant

For a finite `S ⊆ ℕ` with elements `r₁ < ⋯ < rₘ`, the derivative of the pole product
`D_S(t) = ∏_{r ∈ S} (t + r²)` at a root `-r₀²` is `D_S'(-r₀²) = ∏_{r ∈ S, r ≠ r₀} (r² - r₀²)`.
Grouping the ordered pairs `(r, r₀)` with `r ≠ r₀` into unordered pairs `{r_k, r_l}`, each of
which contributes `-(r_l² - r_k²)²`, gives
`∏_{k < l} (r_l² - r_k²)² / ∏_{r ∈ S} D_S'(-r²) = (-1)^{m(m-1)/2}`.

## Main results

* `Zeta5Irr.prod_prod_erase_sq_sub_sq`: `∏_{r₀ ∈ S} ∏_{r ≠ r₀} (r² - r₀²)
  = (-1)^{m(m-1)/2} ∏_{k < l} (r_l² - r_k²)²`.
* `Zeta5Irr.prod_sq_sub_sq_sq_div_prod_eval_derivative_poleProduct`: the quotient is
  `(-1)^{m(m-1)/2}`.

## Implementation notes

* The source takes `S ⊆ ℤ_{>0}`. Positivity is not needed: distinct natural numbers have
  distinct squares, so `S` is any finite subset of `ℕ`. The values lie in any field of
  characteristic zero rather than `ℚ`.
* The product over `1 ≤ k < l ≤ m` in increasing order is written as the product over pairs
  `r < r'` of elements of `S`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the degree of the determinant).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- The product over ordered pairs of distinct elements of `S` of `r² - r₀²` is
`(-1)^{m(m-1)/2}` times the square of the product over increasing pairs. -/
theorem prod_prod_erase_sq_sub_sq {R : Type*} [CommRing R] (S : Finset ℕ) :
    ∏ r₀ ∈ S, ∏ r ∈ S.erase r₀, ((r : R) ^ 2 - r₀ ^ 2) =
      (-1) ^ (#S * (#S - 1) / 2) * (∏ r ∈ S, ∏ r' ∈ S with r < r', ((r' : R) ^ 2 - r ^ 2)) ^ 2 := by
  rw [← Nat.choose_two_right]
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (ha a h)
    have h1 : ∏ r₀ ∈ s, ∏ r ∈ (insert a s).erase r₀, ((r : R) ^ 2 - r₀ ^ 2) =
        (∏ r ∈ s, ((a : R) ^ 2 - r ^ 2)) * ∏ r₀ ∈ s, ∏ r ∈ s.erase r₀, ((r : R) ^ 2 - r₀ ^ 2) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r₀ hr₀ ↦ ?_
      rw [erase_insert_of_ne (by rintro rfl; exact has hr₀),
        prod_insert (fun h ↦ has (mem_of_mem_erase h))]
    have h2 : ∏ r ∈ s, ∏ r' ∈ insert a s with r < r', ((r' : R) ^ 2 - r ^ 2) =
        (∏ r ∈ s, ((a : R) ^ 2 - r ^ 2)) *
          ∏ r ∈ s, ∏ r' ∈ s with r < r', ((r' : R) ^ 2 - r ^ 2) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r hr ↦ ?_
      simp only [filter_insert, ha r hr, ↓reduceIte]
      rw [prod_insert (fun h ↦ has (mem_of_mem_filter _ h))]
    have h3 : ∏ r' ∈ insert a s with a < r', ((r' : R) ^ 2 - a ^ 2) = 1 := by
      rw [filter_eq_empty_iff.2, prod_empty]
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact lt_irrefl _
      · exact (ha x hx).not_gt
    rw [prod_insert has, prod_insert has, h1, h2, h3, erase_insert has, ih,
      card_insert_of_notMem has, Nat.choose_succ_left _ _ (by norm_num), Nat.choose_one_right,
      pow_add]
    have : ∏ r ∈ s, ((r : R) ^ 2 - a ^ 2) = (-1) ^ #s * ∏ r ∈ s, ((a : R) ^ 2 - r ^ 2) := by
      rw [← prod_neg]
      exact prod_congr rfl fun _ _ ↦ by ring
    rw [this]
    ring

/-- **The sign of the determinant.** For a finite `S ⊆ ℕ` of cardinality `m`,
`∏_{r < r'} (r'² - r²)² / ∏_{r ∈ S} D_S'(-r²) = (-1)^{m(m-1)/2}`, where the product in the
numerator runs over pairs `r < r'` of elements of `S`. -/
@[zeta5irr "lem_det_sign"]
theorem prod_sq_sub_sq_sq_div_prod_eval_derivative_poleProduct {K : Type*} [Field K] [CharZero K]
    (S : Finset ℕ) :
    (∏ r ∈ S, ∏ r' ∈ S with r < r', ((r' : K) ^ 2 - r ^ 2) ^ 2) /
        ∏ r ∈ S, (derivative (poleProduct S K)).eval (-(r : K) ^ 2) =
      (-1) ^ (#S * (#S - 1) / 2) := by
  rw [prod_congr rfl fun r hr ↦ eval_derivative_poleProduct_neg_sq hr, prod_prod_erase_sq_sub_sq]
  have hQ : ∏ r ∈ S, ∏ r' ∈ S with r < r', ((r' : K) ^ 2 - r ^ 2) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun r _ ↦ prod_ne_zero_iff.2 fun r' hr' ↦ sub_ne_zero.2 ?_
    have := (mem_filter.1 hr').2
    exact_mod_cast (Nat.pow_lt_pow_left this two_ne_zero).ne'
  simp_rw [prod_pow]
  rw [div_eq_iff (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ hQ)),
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end Zeta5Irr
