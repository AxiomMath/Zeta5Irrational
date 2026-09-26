/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qi

/-!
# The pole-weighted basis `f_i`

For `i ≥ 0` the polynomial `f_i ∈ ℚ[t]` is
`f_i(t) = (D_N(t) / (N!) ^ 2) ^ 3 · q_i(t)`,
where `D_N(t) = ∏_{j = 1}^{N} (t + j ^ 2)` is the pole product of `{1, …, N}` and
`q_i` is the integer-valued basis. The normalisation by `(N!) ^ 2 = D_N(0)` makes the
factor `D_N / (N!) ^ 2` take the value `1` at `t = 0`. Since `q_i` has degree `i`,
`f_i` has degree `3N + i`.

## Main definitions

* `Zeta5Irr.poleWeightedBasis`: the polynomial `f_i`, for a given inner degree `N`.

## Main results

* `Zeta5Irr.poleWeightedBasis_zero`: `f_0 = (D_N / (N!) ^ 2) ^ 3`.
* `Zeta5Irr.eval_poleWeightedBasis`: the value of `f_i` at a point.
* `Zeta5Irr.poleWeightedBasis_ne_zero`: `f_i ≠ 0`.
* `Zeta5Irr.natDegree_poleWeightedBasis`: `f_i` has degree `3N + i`.

## Implementation notes

* The source fixes `N = 3n`; here `N` is an arbitrary natural number, passed explicitly,
  and the source's `f_i` is `poleWeightedBasis (innerDegree n) i`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7: the integer-valued basis.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The pole-weighted basis polynomial
`f_i(t) = (D_N(t) / (N!) ^ 2) ^ 3 · q_i(t) ∈ ℚ[t]`. -/
@[zeta5irr "def_fi"]
noncomputable def poleWeightedBasis (N i : ℕ) : ℚ[X] :=
  (C (1 / ((N.factorial : ℚ) ^ 2)) * poleProductRange N ℚ) ^ 3 * integerValuedBasis i

variable (N i : ℕ)

/-- `f_0 = (D_N / (N!) ^ 2) ^ 3`. -/
@[simp]
theorem poleWeightedBasis_zero :
    poleWeightedBasis N 0 = (C (1 / ((N.factorial : ℚ) ^ 2)) * poleProductRange N ℚ) ^ 3 := by
  simp [poleWeightedBasis]

/-- The value of `f_i` at `t` is `(D_N(t) / (N!) ^ 2) ^ 3 · q_i(t)`. -/
theorem eval_poleWeightedBasis (t : ℚ) :
    (poleWeightedBasis N i).eval t =
      ((poleProductRange N ℚ).eval t / (N.factorial : ℚ) ^ 2) ^ 3 *
        (integerValuedBasis i).eval t := by
  simp only [poleWeightedBasis, eval_mul, eval_pow, eval_C]
  ring

/-- The normalising scalar `1 / (N!) ^ 2` is nonzero. -/
theorem one_div_factorial_sq_ne_zero : (1 / ((N.factorial : ℚ) ^ 2)) ≠ 0 := by
  have := N.factorial_ne_zero
  positivity

/-- `f_i ≠ 0`. -/
theorem poleWeightedBasis_ne_zero : poleWeightedBasis N i ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (mul_ne_zero (C_ne_zero.mpr (one_div_factorial_sq_ne_zero N))
    (poleProductRange_ne_zero N ℚ))) (integerValuedBasis_ne_zero i)

/-- `f_i` has degree `3N + i`. -/
@[simp]
theorem natDegree_poleWeightedBasis : (poleWeightedBasis N i).natDegree = 3 * N + i := by
  rw [poleWeightedBasis, natDegree_mul (pow_ne_zero _ (mul_ne_zero
      (C_ne_zero.mpr (one_div_factorial_sq_ne_zero N)) (poleProductRange_ne_zero N ℚ)))
      (integerValuedBasis_ne_zero i), natDegree_pow, natDegree_C_mul
      (one_div_factorial_sq_ne_zero N), natDegree_poleProductRange,
    natDegree_integerValuedBasis]

end Zeta5Irr
