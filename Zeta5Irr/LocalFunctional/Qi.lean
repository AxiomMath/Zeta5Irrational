/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleProductRange

/-!
# The integer-valued basis `q_i`

The polynomials `q_i ∈ ℚ[t]` are defined by `q_0(t) = 1` and, for `i ≥ 1`,
`q_i(t) = (-1) ^ i · 2t · D_{i-1}(t) / (2i)!`, where
`D_m(t) = ∏_{j = 1}^{m} (t + j ^ 2)` is the pole product of `{1, …, m}`.
The polynomial `q_i` has degree exactly `i`, so `(q_i)_{i ≥ 0}` is a basis of `ℚ[t]`.

## Main definitions

* `Zeta5Irr.integerValuedBasis`: the polynomial `q_i`.

## Main results

* `Zeta5Irr.integerValuedBasis_zero`: `q_0 = 1`.
* `Zeta5Irr.integerValuedBasis_succ`:
  `q_{i+1} = (-1) ^ (i + 1) · 2 / (2(i + 1))! · t · D_i`.
* `Zeta5Irr.integerValuedBasis_eq`: the uniform formula for `i ≥ 1`.
* `Zeta5Irr.eval_integerValuedBasis_succ`: the value of `q_{i+1}` at a point.
* `Zeta5Irr.natDegree_integerValuedBasis`: `q_i` has degree `i`.
* `Zeta5Irr.leadingCoeff_integerValuedBasis_succ`: the leading coefficient of `q_{i+1}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7: the integer-valued basis.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The integer-valued basis polynomial `q_i ∈ ℚ[t]`: `q_0 = 1` and, for `i ≥ 1`,
`q_i(t) = (-1) ^ i · 2t · D_{i-1}(t) / (2i)!`. -/
@[zeta5irr "def_qi"]
noncomputable def integerValuedBasis : ℕ → ℚ[X]
  | 0 => 1
  | i + 1 => C ((-1 : ℚ) ^ (i + 1) * 2 / (2 * (i + 1)).factorial) * X * poleProductRange i ℚ

/-- `q_0 = 1`. -/
@[zeta5irr "def_qi", simp]
theorem integerValuedBasis_zero : integerValuedBasis 0 = 1 := rfl

/-- `q_{i+1} = (-1) ^ (i + 1) · 2 / (2(i + 1))! · t · D_i`. -/
@[zeta5irr "def_qi"]
theorem integerValuedBasis_succ (i : ℕ) :
    integerValuedBasis (i + 1) =
      C ((-1 : ℚ) ^ (i + 1) * 2 / (2 * (i + 1)).factorial) * X * poleProductRange i ℚ := rfl

/-- For `i ≥ 1`, `q_i = (-1) ^ i · 2t · D_{i-1} / (2i)!`. -/
theorem integerValuedBasis_eq {i : ℕ} (hi : 1 ≤ i) :
    integerValuedBasis i =
      C ((-1 : ℚ) ^ i * 2 / (2 * i).factorial) * X * poleProductRange (i - 1) ℚ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  simp [integerValuedBasis_succ]

/-- The value of `q_{i+1}` at `t`:
`(-1) ^ (i + 1) · 2t · ∏_{j=1}^{i} (t + j ^ 2) / (2(i + 1))!`. -/
theorem eval_integerValuedBasis_succ (i : ℕ) (t : ℚ) :
    (integerValuedBasis (i + 1)).eval t =
      (-1) ^ (i + 1) * 2 * t * (∏ j ∈ Finset.Icc 1 i, (t + (j : ℚ) ^ 2)) /
        (2 * (i + 1)).factorial := by
  rw [integerValuedBasis_succ, eval_mul, eval_mul, eval_C, eval_X, eval_poleProductRange]
  ring

/-- The scalar in front of `q_{i+1}` is nonzero. -/
theorem integerValuedBasis_coeff_ne_zero (i : ℕ) :
    ((-1 : ℚ) ^ (i + 1) * 2 / (2 * (i + 1)).factorial) ≠ 0 := by
  have := (2 * (i + 1)).factorial_ne_zero
  positivity

/-- The leading coefficient of `q_{i+1}` is `(-1) ^ (i + 1) · 2 / (2(i + 1))!`. -/
theorem leadingCoeff_integerValuedBasis_succ (i : ℕ) :
    (integerValuedBasis (i + 1)).leadingCoeff =
      (-1 : ℚ) ^ (i + 1) * 2 / (2 * (i + 1)).factorial := by
  rw [integerValuedBasis_succ, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_X, (monic_poleProductRange i ℚ).leadingCoeff, mul_one, mul_one]

/-- `q_i ≠ 0`. -/
theorem integerValuedBasis_ne_zero (i : ℕ) : integerValuedBasis i ≠ 0 := by
  cases i with
  | zero => simp
  | succ i =>
    rw [← leadingCoeff_ne_zero, leadingCoeff_integerValuedBasis_succ]
    exact integerValuedBasis_coeff_ne_zero i

/-- `q_i` has degree `i`. -/
@[simp]
theorem natDegree_integerValuedBasis (i : ℕ) : (integerValuedBasis i).natDegree = i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [integerValuedBasis_succ, natDegree_mul, natDegree_C_mul_X _
      (integerValuedBasis_coeff_ne_zero i), natDegree_poleProductRange, add_comm]
    · exact mul_ne_zero (C_ne_zero.mpr (integerValuedBasis_coeff_ne_zero i)) X_ne_zero
    · exact poleProductRange_ne_zero i ℚ

/-- `q_i` has degree `i`, stated with `Polynomial.degree`. -/
theorem degree_integerValuedBasis (i : ℕ) : (integerValuedBasis i).degree = i := by
  rw [degree_eq_natDegree (integerValuedBasis_ne_zero i), natDegree_integerValuedBasis]

end Zeta5Irr
