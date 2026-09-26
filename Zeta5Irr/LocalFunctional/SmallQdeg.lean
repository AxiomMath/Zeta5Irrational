/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qi

/-!
# The top term of the integer-valued basis `q_i`

For `i ≥ 1` the polynomial `q_i(t) = (-1) ^ i · 2t · D_{i-1}(t) / (2i)!` agrees with its
top monomial `(-1) ^ i · 2 / (2i)! · t ^ i` up to terms of degree less than `i`: since
`D_{i-1}` is monic of degree `i - 1`, the polynomial `t · D_{i-1}(t)` is monic of degree `i`,
so `t · D_{i-1}(t) - t ^ i` has degree less than `i`.

## Main results

* `Zeta5Irr.degree_integerValuedBasis_sub_lt`: for `i ≥ 1`,
  `deg (q_i - (-1) ^ i · 2 / (2i)! · t ^ i) < i`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7 (The integer-valued basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- For `i ≥ 1`, the polynomial `q_i(t) - (-1) ^ i · 2 / (2i)! · t ^ i` has degree less
than `i`. -/
@[zeta5irr "lem_small_qdeg"]
theorem degree_integerValuedBasis_sub_lt {i : ℕ} (hi : 1 ≤ i) :
    (integerValuedBasis i - C ((-1 : ℚ) ^ i * 2 / (2 * i).factorial) * X ^ i).degree
      < (i : WithBot ℕ) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  have hm : (X * poleProductRange i ℚ).Monic := monic_X.mul (monic_poleProductRange i ℚ)
  have hdeg : (X * poleProductRange i ℚ).degree = ((i + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_poleProductRange, degree_X, add_comm]
    rfl
  rw [integerValuedBasis_succ, mul_assoc, ← mul_sub, ← smul_eq_C_mul]
  refine (degree_smul_le _ _).trans_lt ?_
  rw [← hdeg]
  refine degree_sub_lt_left (by rw [hdeg, degree_X_pow]) hm.ne_zero ?_
  rw [hm.leadingCoeff, leadingCoeff_X_pow]

end Zeta5Irr
