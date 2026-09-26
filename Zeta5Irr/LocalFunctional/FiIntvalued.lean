/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Fi
public import Zeta5Irr.LocalFunctional.QiBinom
public import Zeta5Irr.LocalFunctional.DNBinom

/-!
# The basis `f_i` is integer-valued at `-m ^ 2`

For every `i ≥ 0` and every integer `m`, the value `f_i(-m ^ 2)` is an integer, where
`f_i(t) = (D_N(t) / (N!) ^ 2) ^ 3 q_i(t)`.

Indeed `D_N(-m ^ 2) / (N!) ^ 2 = (N - m choose N) (N + m choose N)`, a product of binomial
coefficients at integer arguments; `q_0 = 1`; and for `i ≥ 1`,
`q_i(-m ^ 2) = (m + i choose 2i) + (m + i - 1 choose 2i)`, again a sum of binomial
coefficients at integer arguments.

## Main results

* `Zeta5Irr.exists_eval_integerValuedBasis_neg_sq_eq_intCast`: `q_i(-m ^ 2) ∈ ℤ`.
* `Zeta5Irr.exists_eval_poleProductRange_neg_sq_eq_intCast`: `D_N(-m ^ 2) / (N!) ^ 2 ∈ ℤ`.
* `Zeta5Irr.exists_eval_poleWeightedBasis_neg_sq_eq_intCast`: `f_i(-m ^ 2) ∈ ℤ`.

## Implementation notes

* The source fixes `N = 3n`; here `N` is an arbitrary natural number.
* Membership in `ℤ` is stated as the existence of an integer `z` with value `(z : ℚ)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7 (The integer-valued basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- For every `i ≥ 0` and every integer `m`, `q_i(-m ^ 2)` is an integer. -/
theorem exists_eval_integerValuedBasis_neg_sq_eq_intCast (i : ℕ) (m : ℤ) :
    ∃ z : ℤ, (integerValuedBasis i).eval (-(m : ℚ) ^ 2) = z := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact ⟨1, by simp⟩
  · have h := congrArg (eval (m : ℚ)) (integerValuedBasis_comp_neg_X_sq hi)
    simp only [eval_comp, eval_neg, eval_pow, eval_X, eval_add, eval_sub, eval_C,
      eval_one] at h
    refine ⟨Ring.choose (m + i) (2 * i) + Ring.choose (m + i - 1) (2 * i), ?_⟩
    rw [h, Int.cast_add, ← eval_intCast_qbinom, ← eval_intCast_qbinom]
    push_cast
    rfl

/-- For every integer `m`, `D_N(-m ^ 2) / (N!) ^ 2` is an integer. -/
theorem exists_eval_poleProductRange_neg_sq_eq_intCast (N : ℕ) (m : ℤ) :
    ∃ z : ℤ, (poleProductRange N ℚ).eval (-(m : ℚ) ^ 2) / (N.factorial : ℚ) ^ 2 = z := by
  refine ⟨Ring.choose (N - m) N * Ring.choose (N + m) N, ?_⟩
  rw [div_eq_inv_mul, ← one_div, eval_poleProductRange_neg_sq, Int.cast_mul,
    ← eval_intCast_qbinom, ← eval_intCast_qbinom]
  push_cast
  rfl

/-- **`f_i` is integer-valued at `-m ^ 2`.** For every `i ≥ 0` and every integer `m`,
`f_i(-m ^ 2) ∈ ℤ`. -/
@[zeta5irr "lem_fi_intvalued"]
theorem exists_eval_poleWeightedBasis_neg_sq_eq_intCast (N i : ℕ) (m : ℤ) :
    ∃ z : ℤ, (poleWeightedBasis N i).eval (-(m : ℚ) ^ 2) = z := by
  obtain ⟨a, ha⟩ := exists_eval_poleProductRange_neg_sq_eq_intCast N m
  obtain ⟨b, hb⟩ := exists_eval_integerValuedBasis_neg_sq_eq_intCast i m
  exact ⟨a ^ 3 * b, by rw [eval_poleWeightedBasis, ha, hb]; push_cast; rfl⟩

end Zeta5Irr
