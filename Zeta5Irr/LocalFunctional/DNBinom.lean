/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.LocalFunctional.Qbinom

/-!
# `D_N(-x²)` as a product of two binomial polynomials

In `ℚ[x]` one has
`D_N(-x ^ 2) / (N!) ^ 2 = (N - x choose N) * (N + x choose N)`.
Indeed `D_N(-x ^ 2) = ∏_{j = 1}^{N} (j ^ 2 - x ^ 2) = ∏_{j = 1}^{N} (j - x) (j + x)`, while
reindexing the falling factorial by `j = N - m` gives
`(N + x choose N) = (1 / N!) ∏_{j = 1}^{N} (x + j)` and
`(N - x choose N) = (1 / N!) ∏_{j = 1}^{N} (j - x)`.

## Main results

* `Zeta5Irr.poleProductRange_comp_neg_X_sq`: the polynomial identity
  `D_N(-x ^ 2) / (N!) ^ 2 = (N - x choose N) (N + x choose N)`.
* `Zeta5Irr.eval_poleProductRange_neg_sq`: its evaluated form at `x ∈ ℚ`.

## Implementation notes

Substitution of `-x ^ 2`, `N - x` and `N + x` is expressed with `Polynomial.comp`, and division
by `(N!) ^ 2` as multiplication by the constant polynomial `C (1 / (N!) ^ 2)`, matching the
normalisation used for the pole-weighted basis. The identity is proved pointwise and then
lifted to polynomials, as `ℚ` is infinite.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7 (The integer-valued basis).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial Nat

/-- Pointwise form: for `x ∈ ℚ`,
`D_N(-x ^ 2) / (N!) ^ 2 = (N - x choose N) (N + x choose N)`. -/
theorem eval_poleProductRange_neg_sq (N : ℕ) (x : ℚ) :
    1 / (N ! : ℚ) ^ 2 * (poleProductRange N ℚ).eval (-x ^ 2) =
      (qbinom N).eval (N - x) * (qbinom N).eval (N + x) := by
  rw [poleProductRange_eq_prod_range, eval_prod, eval_qbinom, eval_qbinom]
  have h₁ : ∏ i ∈ range N, ((N : ℚ) - x - i) = ∏ i ∈ range N, ((i + 1 : ℕ) - x : ℚ) := by
    rw [← prod_range_reflect]
    refine prod_congr rfl fun i hi => ?_
    have := mem_range.1 hi
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have h₂ : ∏ i ∈ range N, ((N : ℚ) + x - i) = ∏ i ∈ range N, ((i + 1 : ℕ) + x : ℚ) := by
    rw [← prod_range_reflect]
    refine prod_congr rfl fun i hi => ?_
    have := mem_range.1 hi
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h₁, h₂]
  have h₃ : ∏ i ∈ range N, (X + C (((i + 1 : ℕ) : ℚ) ^ 2)).eval (-x ^ 2) =
      (∏ i ∈ range N, ((i + 1 : ℕ) - x : ℚ)) * ∏ i ∈ range N, ((i + 1 : ℕ) + x : ℚ) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp only [eval_add, eval_X, eval_C]
    ring
  rw [h₃]
  field_simp

/-- **`D_N(-x²)` as a product of binomial polynomials.** In `ℚ[x]`,
`D_N(-x ^ 2) / (N!) ^ 2 = (N - x choose N) (N + x choose N)`. -/
@[zeta5irr "lem_DN_binom"]
theorem poleProductRange_comp_neg_X_sq (N : ℕ) :
    C (1 / (N ! : ℚ) ^ 2) * (poleProductRange N ℚ).comp (-X ^ 2) =
      (qbinom N).comp (C (N : ℚ) - X) * (qbinom N).comp (C (N : ℚ) + X) := by
  refine Polynomial.funext fun x => ?_
  simp only [eval_mul, eval_C, eval_comp, eval_neg, eval_pow, eval_X, eval_sub, eval_add]
  exact eval_poleProductRange_neg_sq N x

end Zeta5Irr
