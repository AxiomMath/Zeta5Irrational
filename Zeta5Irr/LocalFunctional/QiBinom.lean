/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qi
public import Zeta5Irr.LocalFunctional.Qbinom

/-!
# The basis `q_i` in terms of binomial polynomials

For every `i ≥ 1`, in `ℚ[x]`,
`q_i(-x ^ 2) = (x + i choose 2i) + (x + i - 1 choose 2i)`.

Both sides equal `2x ^ 2 ∏_{j=1}^{i-1} (x ^ 2 - j ^ 2) / (2i)!`. On the left this is the
definition of `q_i` together with `D_{i-1}(-x ^ 2) = (-1) ^ (i - 1) ∏_{j=1}^{i-1} (x ^ 2 - j ^ 2)`.
On the right, the two falling factorials `∏_{k=-i+1}^{i} (x + k)` and `∏_{k=-i}^{i-1} (x + k)`
share the factor `∏_{k=-i+1}^{i-1} (x + k) = x ∏_{j=1}^{i-1} (x ^ 2 - j ^ 2)`, and the remaining
factors sum to `(x + i) + (x - i) = 2x`.

## Main results

* `Zeta5Irr.descPochhammer_comp_X_add_natCast`: the symmetric falling factorial
  `∏_{k=-n}^{n} (x + k) = x ∏_{j=1}^{n} (x ^ 2 - j ^ 2)`.
* `Zeta5Irr.integerValuedBasis_comp_neg_X_sq`: `q_i(-x ^ 2)` as a sum of two binomial
  polynomials.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7 (The integer-valued basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- The symmetric falling factorial: `∏_{k=-n}^{n} (x + k) = x ∏_{j=1}^{n} (x ^ 2 - j ^ 2)`,
written as the falling factorial of length `2n + 1` evaluated at `x + n`. -/
theorem descPochhammer_comp_X_add_natCast (n : ℕ) :
    (descPochhammer ℚ (2 * n + 1)).comp (X + C (n : ℚ)) =
      X * ∏ j ∈ range n, (X ^ 2 - C (((j + 1 : ℕ) : ℚ) ^ 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, descPochhammer_succ_left,
      descPochhammer_succ_right]
    simp only [mul_comp, sub_comp, X_comp, natCast_comp, one_comp, comp_assoc]
    rw [show X + C ((n + 1 : ℕ) : ℚ) - 1 = X + C (n : ℚ) by push_cast; rw [C_add, C_1]; ring,
      ih, prod_range_succ]
    simp only [map_pow, map_natCast]
    push_cast
    ring

/-- The sum of the two falling factorials of length `2n + 2` at `x + n + 1` and at `x + n`:
`∏_{k=-n}^{n+1} (x + k) + ∏_{k=-n-1}^{n} (x + k) = 2x ^ 2 ∏_{j=1}^{n} (x ^ 2 - j ^ 2)`. -/
theorem descPochhammer_comp_add_descPochhammer_comp (n : ℕ) :
    (descPochhammer ℚ (2 * n + 2)).comp (X + C ((n + 1 : ℕ) : ℚ)) +
      (descPochhammer ℚ (2 * n + 2)).comp (X + C ((n + 1 : ℕ) : ℚ) - 1) =
      2 * X ^ 2 * ∏ j ∈ range n, (X ^ 2 - C (((j + 1 : ℕ) : ℚ) ^ 2)) := by
  have hn : X + C ((n + 1 : ℕ) : ℚ) - 1 = X + C (n : ℚ) := by
    push_cast; rw [C_add, C_1]; ring
  nth_rw 1 [descPochhammer_succ_left ℚ (2 * n + 1)]
  rw [descPochhammer_succ_right ℚ (2 * n + 1), mul_comp, mul_comp, X_comp, comp_assoc, sub_comp,
    X_comp, one_comp, hn, sub_comp, X_comp, natCast_comp, descPochhammer_comp_X_add_natCast]
  simp only [map_natCast]
  push_cast
  ring

/-- For every `i ≥ 1`, `q_i(-x ^ 2) = (x + i choose 2i) + (x + i - 1 choose 2i)` in `ℚ[x]`. -/
@[zeta5irr "lem_qi_binom"]
theorem integerValuedBasis_comp_neg_X_sq {i : ℕ} (hi : 1 ≤ i) :
    (integerValuedBasis i).comp (-X ^ 2) =
      (qbinom (2 * i)).comp (X + C (i : ℚ)) + (qbinom (2 * i)).comp (X + C (i : ℚ) - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rw [qbinom, smul_comp, smul_comp, ← smul_add, show 2 * (n + 1) = 2 * n + 2 by ring,
    descPochhammer_comp_add_descPochhammer_comp, integerValuedBasis_succ,
    poleProductRange_eq_prod_range, mul_comp, mul_comp, C_comp, X_comp, Polynomial.prod_comp]
  simp only [add_comp, X_comp, C_comp]
  rw [show ∏ j ∈ range n, (-X ^ 2 + C (((j + 1 : ℕ) : ℚ) ^ 2)) =
      ∏ j ∈ range n, -(X ^ 2 - C (((j + 1 : ℕ) : ℚ) ^ 2)) from
      prod_congr rfl fun _ _ ↦ by ring, prod_neg, card_range, smul_eq_C_mul]
  rw [show 2 * n + 2 = 2 * (n + 1) by ring]
  have h : ((-1 : ℚ[X]) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  simp only [div_eq_mul_inv, map_mul, map_pow, map_neg, map_one, map_ofNat]
  linear_combination (C ((2 * (n + 1)).factorial : ℚ)⁻¹ * 2 * X ^ 2 *
    ∏ j ∈ range n, (X ^ 2 - C ((j + 1 : ℕ) : ℚ) ^ 2)) * h

end Zeta5Irr
