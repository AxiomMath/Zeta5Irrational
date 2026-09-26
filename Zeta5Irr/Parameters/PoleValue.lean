/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs

/-!
# The pole values

For `j ≥ 1` the pole value is the linear polynomial
`ν_j(X) = j ^ 4 (X - H_j^{(5)}) - 1/4 + 1/(2j) ∈ ℚ[X]`.
It is the value of the functional of the construction on the simple pole `1 / (t + j ^ 2)`,
as a polynomial in the indeterminate `X` which is later specialised to `ξ = ζ(5)`.
It has degree one in `X`, with leading coefficient `j ^ 4`.

## Main definitions

* `Zeta5Irr.poleValue`: the pole value `ν_j(X)`.

## Main results

* `Zeta5Irr.eval_poleValue`, `Zeta5Irr.aeval_poleValue`: the value of `ν_j` at a point of
  `ℚ`, and of an arbitrary `ℚ`-algebra (such as `ℝ`, where `X = ξ`).
* `Zeta5Irr.coeff_zero_poleValue`, `Zeta5Irr.coeff_one_poleValue`: the coefficients of `ν_j`.
* `Zeta5Irr.natDegree_poleValue`, `Zeta5Irr.leadingCoeff_poleValue`: for `j ≠ 0`, `ν_j` has
  degree one and leading coefficient `j ^ 4`.

## Implementation notes

* The source defines `ν_j` only for `j ≥ 1`. Here `j` ranges over `ℕ`; at `j = 0` Lean's
  convention `1 / 0 = 0` makes `ν_0 = -1/4`, a value that is never used. Results that need
  `j ≥ 1` carry the hypothesis `j ≠ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The pole value `ν_j(X) = j ^ 4 (X - H_j^{(5)}) - 1/4 + 1/(2j) ∈ ℚ[X]`, the value of the
functional on the simple pole `1 / (t + j ^ 2)`. -/
@[zeta5irr "def_polevalue"]
noncomputable def poleValue (j : ℕ) : ℚ[X] :=
  C ((j : ℚ) ^ 4) * (X - C (harmonicFive j)) - C (1 / 4) + C (1 / (2 * (j : ℚ)))

/-- `ν_j` as `j ^ 4 X + c`: a linear polynomial with explicit coefficients. -/
theorem poleValue_eq (j : ℕ) :
    poleValue j = C ((j : ℚ) ^ 4) * X +
      C (-((j : ℚ) ^ 4 * harmonicFive j) - 1 / 4 + 1 / (2 * (j : ℚ))) := by
  simp only [poleValue, C_add, C_sub, C_neg, C_mul]
  ring

/-- The value of `ν_j` at a rational point `x`. -/
@[simp]
theorem eval_poleValue (j : ℕ) (x : ℚ) :
    (poleValue j).eval x = (j : ℚ) ^ 4 * (x - harmonicFive j) - 1 / 4 + 1 / (2 * (j : ℚ)) := by
  simp [poleValue]

/-- The value of `ν_j` at a point `x` of a `ℚ`-algebra `A`, such as `x = ξ ∈ ℝ`. -/
@[simp]
theorem aeval_poleValue {A : Type*} [CommRing A] [Algebra ℚ A] (j : ℕ) (x : A) :
    aeval x (poleValue j) =
      (j : A) ^ 4 * (x - algebraMap ℚ A (harmonicFive j)) - algebraMap ℚ A (1 / 4) +
        algebraMap ℚ A (1 / (2 * (j : ℚ))) := by
  simp [poleValue]

/-- The coefficient of `X` in `ν_j` is `j ^ 4`. -/
@[simp]
theorem coeff_one_poleValue (j : ℕ) : (poleValue j).coeff 1 = (j : ℚ) ^ 4 := by
  rw [poleValue_eq, coeff_add, coeff_C_mul_X, coeff_C]
  simp

/-- The constant coefficient of `ν_j` is `-j ^ 4 H_j^{(5)} - 1/4 + 1/(2j)`. -/
@[simp]
theorem coeff_zero_poleValue (j : ℕ) :
    (poleValue j).coeff 0 = -((j : ℚ) ^ 4 * harmonicFive j) - 1 / 4 + 1 / (2 * (j : ℚ)) := by
  rw [poleValue_eq, coeff_add, coeff_C_mul_X, coeff_C_zero]
  simp

/-- `ν_j` has degree at most one in `X`. -/
theorem natDegree_poleValue_le (j : ℕ) : (poleValue j).natDegree ≤ 1 := by
  rw [poleValue_eq]
  exact natDegree_linear_le

/-- `ν_j` has degree at most one in `X`. -/
theorem degree_poleValue_le (j : ℕ) : (poleValue j).degree ≤ 1 := by
  rw [poleValue_eq]
  exact degree_linear_le

/-- For `j ≠ 0`, `ν_j` has degree exactly one in `X`. -/
@[simp]
theorem natDegree_poleValue {j : ℕ} (hj : j ≠ 0) : (poleValue j).natDegree = 1 := by
  rw [poleValue_eq]
  exact natDegree_linear (by positivity)

/-- For `j ≠ 0`, `ν_j` has degree exactly one in `X`. -/
theorem degree_poleValue {j : ℕ} (hj : j ≠ 0) : (poleValue j).degree = 1 := by
  rw [poleValue_eq]
  exact degree_linear (by positivity)

/-- For `j ≠ 0`, the leading coefficient of `ν_j` is `j ^ 4`. -/
@[simp]
theorem leadingCoeff_poleValue {j : ℕ} (hj : j ≠ 0) :
    (poleValue j).leadingCoeff = (j : ℚ) ^ 4 := by
  rw [poleValue_eq]
  exact leadingCoeff_linear (by positivity)

/-- For `j ≠ 0`, `ν_j` is a nonzero polynomial. -/
theorem poleValue_ne_zero {j : ℕ} (hj : j ≠ 0) : poleValue j ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_poleValue hj]; exact one_pos)

end Zeta5Irr
