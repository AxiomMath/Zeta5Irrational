/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.NormalizedDeterminant
public import Zeta5Irr.Parameters.MuXSmul
public import Zeta5Irr.LocalFunctional.Fi

/-!
# `F_K` as a determinant in the integer-valued basis

With `K = 40 n`, `N = 3 n` and `h = 37 n`, the normalized determinant `F_K(X) = S_K Δ_K(X)` is
the Gram determinant of the pole-weighted basis `f_0, …, f_{h-1}` for the rational functional:
`F_K(X) = det [(K!)² μ_X(f_i(t) f_j(t); {1, …, K})]_{0 ≤ i, j < h}`.

Let `B` be the `h × h` rational matrix with `B_{ik}` the coefficient of `t ^ k` in `q_i`. Since
`q_i` has degree `i`, the matrix `B` is lower triangular, with `B_{00} = 1` and
`B_{ii} = (-1) ^ i 2 / (2i)!` for `i ≥ 1`, and `q_i = ∑_{k < h} B_{ik} t ^ k`. Expanding
`f_i f_j = (N!)^{-12} D_N ^ 6 q_i q_j` by linearity of `μ_X` gives
`(K!)² μ_X(f_i f_j) = (K!)² (N!)^{-12} (B G_K(X) Bᵀ)_{ij}`, so the determinant is
`(K!)^{2h} (N!)^{-12h} (det B)² Δ_K(X)`, and `(det B)² = 4^{h-1} / ∏_{i=1}^{h-1} ((2i)!)²`
makes the prefactor exactly `S_K`.

## Main definitions

* `Zeta5Irr.integerValuedBasisCoeffMatrix`: the coefficient matrix `B` of `q_0, …, q_{h-1}`.

## Main results

* `Zeta5Irr.sq_det_integerValuedBasisCoeffMatrix`:
  `(det B)² = 4^{h-1} / ∏_{i=1}^{h-1} ((2i)!)²`.
* `Zeta5Irr.rationalFunctional_poleWeightedBasis_mul`: `μ_X(f_i f_j; S)` expanded in the
  monomial basis.
* `Zeta5Irr.normalizedDet_eq_det_rationalFunctional_poleWeightedBasis`:
  `F_K(X) = det [(K!)² μ_X(f_i f_j; {1, …, K})]_{0 ≤ i, j < h}`.

## Implementation notes

* Rows and columns are indexed by `Fin h`; the scalar `(K!)²` enters the matrix entries as the
  constant polynomial `C ((K!)²)`, and `{1, …, K}` is `Finset.Icc 1 K`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7 (The integer-valued basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- The `h × h` coefficient matrix `B` of the integer-valued basis: `B_{ik}` is the
coefficient of `t ^ k` in `q_i`, for `0 ≤ i, k < h`. -/
noncomputable def integerValuedBasisCoeffMatrix (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  Matrix.of fun i k => (integerValuedBasis i).coeff k

/-- For `i < h`, `q_i = ∑_{k < h} B_{ik} t ^ k`. -/
theorem integerValuedBasis_eq_sum_coeffMatrix {h : ℕ} (i : Fin h) :
    integerValuedBasis i =
      ∑ k : Fin h, C (integerValuedBasisCoeffMatrix h i k) * X ^ (k : ℕ) := by
  simp only [integerValuedBasisCoeffMatrix, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => C ((integerValuedBasis i).coeff k) * X ^ k)]
  conv_lhs => rw [as_sum_range' (integerValuedBasis i) h (by simp)]
  simp [C_mul_X_pow_eq_monomial]

/-- The coefficient matrix `B` is lower triangular, since `q_i` has degree `i`. -/
theorem integerValuedBasisCoeffMatrix_blockTriangular (h : ℕ) :
    (integerValuedBasisCoeffMatrix h).BlockTriangular OrderDual.toDual := by
  intro i k hik
  simp only [integerValuedBasisCoeffMatrix, Matrix.of_apply]
  apply coeff_eq_zero_of_natDegree_lt
  simpa using hik

/-- The squared diagonal entries of `B`: `B_{00}² = 1` and `B_{ii}² = 4 / ((2i)!)²` for
`i ≥ 1`. -/
theorem integerValuedBasisCoeffMatrix_diag_sq {h : ℕ} (i : Fin h) :
    integerValuedBasisCoeffMatrix h i i ^ 2 =
      if (i : ℕ) = 0 then 1 else 4 / (((2 * (i : ℕ)).factorial : ℕ) : ℚ) ^ 2 := by
  simp only [integerValuedBasisCoeffMatrix, Matrix.of_apply]
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero => simp
  | succ m =>
    have := leadingCoeff_integerValuedBasis_succ m
    rw [leadingCoeff, natDegree_integerValuedBasis] at this
    simp only [this, Nat.succ_ne_zero, ite_false]
    rw [div_pow, mul_pow, ← pow_mul, mul_comm (m + 1) 2, pow_mul]
    norm_num

/-- `(det B)² = 4^{h-1} / ∏_{i=1}^{h-1} ((2i)!)²`. -/
theorem sq_det_integerValuedBasisCoeffMatrix (h : ℕ) :
    (integerValuedBasisCoeffMatrix h).det ^ 2 =
      4 ^ (h - 1) / ∏ i ∈ Icc 1 (h - 1), (((2 * i).factorial : ℕ) : ℚ) ^ 2 := by
  rw [Matrix.det_of_isLowerTriangular _ (integerValuedBasisCoeffMatrix_blockTriangular h),
    ← Finset.prod_pow]
  simp only [integerValuedBasisCoeffMatrix_diag_sq]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => if i = 0 then (1 : ℚ) else 4 / (((2 * i).factorial : ℕ) : ℚ) ^ 2)]
  cases h with
  | zero => simp
  | succ m =>
    rw [prod_range_succ', Nat.add_sub_cancel]
    simp only [Nat.succ_ne_zero, ite_false, ite_true, mul_one]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_range_succ, ih, prod_Icc_succ_top (by omega), pow_succ]
      field_simp
      ring

/-- For `i, j < h`, `f_i f_j = ∑_{k, l < h} (N!)^{-12} B_{ik} B_{jl} D_N ^ 6 t ^ (k + l)`. -/
theorem poleWeightedBasis_mul_eq_sum (N : ℕ) {h : ℕ} (i j : Fin h) :
    poleWeightedBasis N i * poleWeightedBasis N j =
      ∑ k : Fin h, ∑ l : Fin h, C ((1 / ((N.factorial : ℚ) ^ 2)) ^ 6 *
        integerValuedBasisCoeffMatrix h i k * integerValuedBasisCoeffMatrix h j l) *
          (poleProductRange N ℚ ^ 6 * X ^ ((k : ℕ) + l)) := by
  rw [poleWeightedBasis, poleWeightedBasis, integerValuedBasis_eq_sum_coeffMatrix i,
    integerValuedBasis_eq_sum_coeffMatrix j, mul_mul_mul_comm, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [C_mul, C_pow, pow_add]
  ring

/-- For `i, j < h`,
`μ_X(f_i f_j; S) = ∑_{k, l < h} (N!)^{-12} B_{ik} B_{jl} μ_X(D_N ^ 6 t ^ (k + l); S)`. -/
theorem rationalFunctional_poleWeightedBasis_mul (S : Finset ℕ) (N : ℕ) {h : ℕ}
    (i j : Fin h) :
    rationalFunctional S (poleWeightedBasis N i * poleWeightedBasis N j) =
      ∑ k : Fin h, ∑ l : Fin h, C ((1 / ((N.factorial : ℚ) ^ 2)) ^ 6 *
        integerValuedBasisCoeffMatrix h i k * integerValuedBasisCoeffMatrix h j l) *
          rationalFunctional S (poleProductRange N ℚ ^ 6 * X ^ ((k : ℕ) + l)) := by
  simp only [poleWeightedBasis_mul_eq_sum, map_sum, rationalFunctional_C_mul]

/-- `F_K(X) = det [(K!)² μ_X(f_i(t) f_j(t); {1, …, K})]_{0 ≤ i, j < h}`, where `K = 40 n`,
`N = 3 n` and `h = 37 n`. -/
@[zeta5irr "lem_FK_basis"]
theorem normalizedDet_eq_det_rationalFunctional_poleWeightedBasis (n : ℕ) :
    normalizedDet n = (Matrix.of fun i j : Fin (matrixOrder n) =>
      C (((poleBound n).factorial : ℚ) ^ 2) *
        rationalFunctional (Icc 1 (poleBound n))
          (poleWeightedBasis (innerDegree n) i * poleWeightedBasis (innerDegree n) j)).det := by
  set B := integerValuedBasisCoeffMatrix (matrixOrder n)
  set c : ℚ :=
    ((poleBound n).factorial : ℚ) ^ 2 * (1 / ((innerDegree n).factorial : ℚ) ^ 2) ^ 6
  have hM : (Matrix.of fun i j : Fin (matrixOrder n) =>
      C (((poleBound n).factorial : ℚ) ^ 2) *
        rationalFunctional (Icc 1 (poleBound n))
          (poleWeightedBasis (innerDegree n) i * poleWeightedBasis (innerDegree n) j)) =
      C c • (B.map C * gramMatrix n * (B.map C).transpose) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, rationalFunctional_poleWeightedBasis_mul, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, gramMatrix_apply,
      smul_eq_mul, mul_sum, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => sum_congr rfl fun k _ => ?_
    simp only [c, C_mul]
    ring
  rw [hM, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, normalizedDet, gramDet, Fintype.card_fin]
  have hS : scalingFactor n = c ^ matrixOrder n * B.det ^ 2 := by
    rw [sq_det_integerValuedBasisCoeffMatrix, scalingFactor]
    have hN : ((innerDegree n).factorial : ℚ) ≠ 0 := by positivity
    simp only [c, one_div, inv_pow, mul_pow, ← pow_mul]
    field_simp
  rw [hS, C_mul, C_pow, C_pow]
  ring

end Zeta5Irr
