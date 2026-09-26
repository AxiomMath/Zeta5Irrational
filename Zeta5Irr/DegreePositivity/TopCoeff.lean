/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramDeterminant
public import Zeta5Irr.Parameters.EntryPoles
public import Zeta5Irr.DegreePositivity.EntryDegree
public import Zeta5Irr.DegreePositivity.EntryDegreeLin

/-!
# The top coefficient of `Δ_K`

Let `K = 40 n`, `N = 3 n` and `h = 37 n`, and write `S = {N + 1, …, K}`, a set with `h`
elements. The coefficient of `X ^ h` in `Δ_K = det G_K(X)` is
`(-1) ^ (h (h - 1) / 2) ∏_{r = N + 1}^{K} r ^ 4 D_N(-r ^ 2) ^ 5`.

The entries of `G_K(X)` are `μ_X(D_N(t) ^ 5 t ^ (i + j); S)`, each of degree at most one in `X`,
so `G_K(X) = 𝒜 + X ℬ` over `ℚ` and the coefficient of `X ^ h` in `Δ_K` is `det ℬ`. The matrix
of coefficients of `X` factors as `ℬ = V 𝒟 Vᵀ`, where `V_{ir} = (-r ^ 2) ^ i` is the transposed
Vandermonde matrix at the nodes `-r ^ 2`, `r ∈ S`, and `𝒟` is diagonal with entries
`r ^ 4 D_N(-r ^ 2) ^ 5 / D_S'(-r ^ 2)`. Hence
`det ℬ = (det V) ^ 2 ∏_{r ∈ S} r ^ 4 D_N(-r ^ 2) ^ 5 / D_S'(-r ^ 2)`, and the sign of the
determinant evaluates `(det V) ^ 2 / ∏_{r ∈ S} D_S'(-r ^ 2)` as `(-1) ^ (h (h - 1) / 2)`.

The argument uses of `D_N(t) ^ 5` and of `S` only that `S` is a finite set of `h` natural
numbers and `D_N(t) ^ 5` a polynomial, and is carried out in that generality first.

## Main results

* `Zeta5Irr.eq_X_smul_map_C_add_map_C_of_natDegree_le_one`: a matrix of polynomials of degree
  at most one is `X • A + B` with constant `A`, `B`.
* `Zeta5Irr.coeff_det_of_natDegree_le_one`: for a square matrix of polynomials of degree at
  most one, the top coefficient of its determinant is the determinant of the matrix of
  coefficients of `X`.
* `Zeta5Irr.det_vandermonde_neg_sq_sq`: the squared Vandermonde determinant at the nodes
  `-r ^ 2`, `r ∈ S`.
* `Zeta5Irr.coeff_det_rationalFunctional_mul_X_pow`: the coefficient of `X ^ #S` in
  `det (μ_X(P(t) t ^ (i + j); S))_{i, j}` for any finite `S ⊆ ℕ` and `P ∈ ℚ[t]`.
* `Zeta5Irr.coeff_gramDet_matrixOrder`: the coefficient of `X ^ h` in `Δ_K`.

## Implementation notes

* The rows and columns of `G_K(X)` are indexed by `Fin h`; the elements of `S` are listed in
  increasing order by `Finset.orderIsoOfFin`, which identifies the product over `k < l` of
  the Vandermonde determinant with the product over pairs `r < r'` of elements of `S`.
* The statement holds for every `n`, including `n = 0`, where both sides equal `1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the degree of the determinant).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- A square polynomial matrix whose entries have degree at most one is `X • A + B` for the
constant matrices `A`, `B` of coefficients of `X` and of `1` of its entries. -/
theorem eq_X_smul_map_C_add_map_C_of_natDegree_le_one {n R : Type*} [CommRing R]
    (M : Matrix n n R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    M = (X : R[X]) • (M.map fun p ↦ p.coeff 1).map C + (M.map fun p ↦ p.coeff 0).map C := by
  ext i j : 1
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (hM i j)]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-- If every entry of a square polynomial matrix `M` has degree at most one, then the
coefficient of `X ^ m` in `det M`, where `m` is the size of `M`, is the determinant of the
matrix of coefficients of `X` of the entries. -/
theorem coeff_det_of_natDegree_le_one {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    M.det.coeff (Fintype.card n) = (M.map fun p ↦ p.coeff 1).det := by
  have := eq_X_smul_map_C_add_map_C_of_natDegree_le_one M hM
  conv_lhs => rw [this]
  rw [coeff_det_X_add_C_card]

/-- The square of the Vandermonde determinant at the nodes `-r ^ 2`, `r ∈ S`, listed in
increasing order, is `∏_{r < r'} (r' ^ 2 - r ^ 2) ^ 2`. -/
theorem det_vandermonde_neg_sq_sq {R : Type*} [CommRing R] (S : Finset ℕ) {m : ℕ}
    (hm : #S = m) :
    (Matrix.vandermonde fun k ↦ -((S.orderIsoOfFin hm k : ℕ) : R) ^ 2).det ^ 2 =
      ∏ r ∈ S, ∏ r' ∈ S with r < r', ((r' : R) ^ 2 - r ^ 2) ^ 2 := by
  set e := S.orderIsoOfFin hm
  rw [Matrix.det_vandermonde, ← prod_pow]
  simp_rw [← prod_pow, prod_filter]
  rw [← prod_coe_sort S]
  simp_rw [← prod_coe_sort S (fun r' ↦ if _ < r' then _ else _)]
  rw [← e.toEquiv.prod_comp]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [← e.toEquiv.prod_comp, ← prod_filter]
  refine prod_congr (by ext j; simp) fun j _ ↦ ?_
  simp only [RelIso.coe_fn_toEquiv]
  ring

/-- For a finite `S ⊆ ℕ` of cardinality `m` and `P ∈ ℚ[t]`, the coefficient of `X ^ m` in the
determinant of the `m × m` Hankel matrix `(μ_X(P(t) t ^ (i + j); S))_{i, j}` is
`(-1) ^ (m (m - 1) / 2) ∏_{r ∈ S} r ^ 4 P(-r ^ 2)`. -/
theorem coeff_det_rationalFunctional_mul_X_pow (S : Finset ℕ) (P : ℚ[X]) {m : ℕ}
    (hm : #S = m) :
    (Matrix.of fun i j : Fin m ↦ rationalFunctional S (P * X ^ ((i : ℕ) + j))).det.coeff m =
      (-1) ^ (m * (m - 1) / 2) * ∏ r ∈ S, (r : ℚ) ^ 4 * P.eval (-(r : ℚ) ^ 2) := by
  set e := S.orderIsoOfFin hm
  set x : Fin m → ℚ := fun k ↦ -((e k : ℕ) : ℚ) ^ 2
  set d : Fin m → ℚ := fun k ↦ ((e k : ℕ) : ℚ) ^ 4 * P.eval (x k) /
    (derivative (poleProduct S ℚ)).eval (x k)
  have hB : ((Matrix.of fun i j : Fin m ↦ rationalFunctional S (P * X ^ ((i : ℕ) + j))).map
      fun p ↦ p.coeff 1) =
      (Matrix.vandermonde x).transpose * Matrix.diagonal d * Matrix.vandermonde x := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, coeff_one_rationalFunctional, eval_mul,
      eval_pow, eval_X, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      Matrix.vandermonde_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    rw [← sum_coe_sort S, ← e.toEquiv.sum_comp]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [RelIso.coe_fn_toEquiv, x, d]
    ring
  have htop := coeff_det_of_natDegree_le_one
    (Matrix.of fun i j : Fin m ↦ rationalFunctional S (P * X ^ ((i : ℕ) + j)))
    fun i j ↦ natDegree_rationalFunctional_le _ _
  rw [Fintype.card_fin] at htop
  rw [htop, hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  have hV : (Matrix.vandermonde x).det ^ 2 =
      ∏ r ∈ S, ∏ r' ∈ S with r < r', ((r' : ℚ) ^ 2 - r ^ 2) ^ 2 :=
    det_vandermonde_neg_sq_sq S hm
  have hd : ∏ k, d k = (∏ r ∈ S, (r : ℚ) ^ 4 * P.eval (-(r : ℚ) ^ 2)) /
      ∏ r ∈ S, (derivative (poleProduct S ℚ)).eval (-(r : ℚ) ^ 2) := by
    rw [← prod_div_distrib, ← prod_coe_sort S, ← e.toEquiv.prod_comp]
    rfl
  rw [mul_right_comm, ← sq, hV, hd, ← mul_div_assoc, mul_div_right_comm,
    prod_sq_sub_sq_sq_div_prod_eval_derivative_poleProduct, hm]

/-- **The top coefficient of `Δ_K`.** With `K = 40 n`, `N = 3 n` and `h = 37 n`, the
coefficient of `X ^ h` in `Δ_K` is
`(-1) ^ (h (h - 1) / 2) ∏_{r = N + 1}^{K} r ^ 4 D_N(-r ^ 2) ^ 5`. -/
@[zeta5irr "lem_top_coeff"]
theorem coeff_gramDet_matrixOrder (n : ℕ) :
    (gramDet n).coeff (matrixOrder n) =
      (-1) ^ (matrixOrder n * (matrixOrder n - 1) / 2) *
        ∏ r ∈ Icc (innerDegree n + 1) (poleBound n),
          (r : ℚ) ^ 4 * (poleProductRange (innerDegree n) ℚ).eval (-(r : ℚ) ^ 2) ^ 5 := by
  have hcard : #(Icc (innerDegree n + 1) (poleBound n)) = matrixOrder n := by
    rw [Nat.card_Icc, ← poleBound_sub_innerDegree]
    omega
  have hG : gramMatrix n = Matrix.of fun i j : Fin (matrixOrder n) ↦
      rationalFunctional (Icc (innerDegree n + 1) (poleBound n))
        (poleProductRange (innerDegree n) ℚ ^ 5 * X ^ ((i : ℕ) + j)) :=
    Matrix.ext (gramMatrix_apply_eq n)
  simp_rw [gramDet, hG, coeff_det_rationalFunctional_mul_X_pow _ _ hcard, eval_pow]

end Zeta5Irr
