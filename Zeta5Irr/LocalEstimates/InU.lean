/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.Rowpoly

/-!
# The coefficient matrix `C^in` of the distributing basis

For an odd prime `p`, an integer `M ≥ 40`, `K ∈ 40 ℤ_{>0}` and `h = 37 n`, the matrix `C^in` has
rows indexed by the pairs `(a, i)` with `0 ≤ a ≤ m°` and `0 ≤ i < L_a`, columns indexed by
`0 ≤ k < h`, and entry at `((a, i), k)` the coefficient of `t^k` in the row polynomial
`Ψ_{a,i}`.

## Main definitions

* `Zeta5Irr.innerCoeffMatrix`: the matrix `C^in`.

## Main results

* `Zeta5Irr.innerCoeffMatrix_apply`: the entry at `((a, i), k)` is the coefficient of `t^k`
  in `Ψ_{a,i}`.
* `Zeta5Irr.card_innerCoeffMatrix_rows`: the number of rows is `∑_{0 ≤ a ≤ m°} L_a`.
* `Zeta5Irr.innerCoeffMatrix_apply_eq_zero_of_lt`: row `(a, i)` vanishes beyond the degree
  of `Ψ_{a,i}`.
* `Zeta5Irr.innerCoeffMatrix_apply_natDegree`: row `(a, i)` has entry `1` at the degree
  of `Ψ_{a,i}`.

## Implementation notes

* The rows are indexed by the sigma type `Σ a : Fin (m° + 1), Fin L_a`, which is exactly the
  set of pairs `(a, i)` of the source. The exponent `L_a` is `Zeta5Irr.rowPolyExponent`, i.e.
  `L_0` for `a = 0` and `L_a` truncated at `0` for `a ≥ 1`; in the range of parameters of the
  source `L_a ≥ 0`, so this is the source's index set.
* The entries are rational, the coefficients of `Ψ_{a,i} ∈ ℚ[t]`.
* The hypotheses on `p`, `M` and `K` are not needed to define `C^in`; the matrix takes `n`
  (with `K = 40 n`, `h = 37 n`), `p` and `M` as arguments, and the lemmas using the
  hypotheses carry them. That the matrix is square is the separate statement that
  `∑_a L_a = h`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The coefficient matrix `C^in` of the distributing basis: rows indexed by the pairs `(a, i)`
with `0 ≤ a ≤ m°` and `0 ≤ i < L_a`, columns by `0 ≤ k < h`, and entry at `((a, i), k)` the
coefficient of `t^k` in the row polynomial `Ψ_{a,i}`. -/
@[zeta5irr "def_in_U"]
noncomputable def innerCoeffMatrix (n p M : ℕ) :
    Matrix (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) (Fin (matrixOrder n)) ℚ :=
  Matrix.of fun ai k => (rowPoly n p M ai.1 ai.2).coeff k

/-- The entry of `C^in` at `((a, i), k)` is the coefficient of `t^k` in `Ψ_{a,i}`. -/
@[simp]
theorem innerCoeffMatrix_apply (n p M : ℕ)
    (ai : Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) (k : Fin (matrixOrder n)) :
    innerCoeffMatrix n p M ai k = (rowPoly n p M ai.1 ai.2).coeff k :=
  rfl

/-- The number of rows of `C^in` is `∑_{0 ≤ a ≤ m°} L_a`. -/
theorem card_innerCoeffMatrix_rows (n p M : ℕ) :
    Fintype.card (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) =
      ∑ a ∈ Finset.range (mStar p + 1), rowPolyExponent n p M a := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun a => rowPolyExponent n p M a) _

/-- Row `(a, i)` of `C^in` vanishes in the columns `k > deg Ψ_{a,i}`. -/
theorem innerCoeffMatrix_apply_eq_zero_of_lt (n p M : ℕ)
    {ai : Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)} {k : Fin (matrixOrder n)}
    (hk : (rowPoly n p M ai.1 ai.2).natDegree < k) :
    innerCoeffMatrix n p M ai k = 0 :=
  coeff_eq_zero_of_natDegree_lt hk

/-- Row `(a, i)` of `C^in` has entry `1` in the column `deg Ψ_{a,i}`, since `Ψ_{a,i}` is
monic. -/
theorem innerCoeffMatrix_apply_natDegree (n p M : ℕ)
    {ai : Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)} {k : Fin (matrixOrder n)}
    (hk : (k : ℕ) = (rowPoly n p M ai.1 ai.2).natDegree) :
    innerCoeffMatrix n p M ai k = 1 := by
  rw [innerCoeffMatrix_apply, hk]
  exact rowPoly_monic n p M ai.1 ai.2

end Zeta5Irr
