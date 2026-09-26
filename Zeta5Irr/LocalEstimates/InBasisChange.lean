/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InForm
public import Zeta5Irr.LocalEstimates.InUnimodular
public import Zeta5Irr.Parameters.GramDeterminant
public import Zeta5Irr.Parameters.EntryPoles
public import Zeta5Irr.LocalFunctional.VpG
public import Zeta5Irr.Parameters.MuXSmul

/-!
# The basis change does not move the valuation

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²` and let `p` be a prime with `K / M < p ≤ K / 3`. Let `B`
be the matrix with rows and columns indexed by the pairs `(a, i)`, `0 ≤ a ≤ m°`, `0 ≤ i < L_a`,
and entries `B_{(a,i),(c,j)} = Φ(Ψ_{a,i}, Ψ_{c,j})`. Then `v_p^G(det B) = v_p^G(Δ_K)`.

The entry `G_K(X)_{kl}` is `Φ(t^k, t^l)`. Writing `Ψ_{a,i} = ∑_{k < h} C^in_{(a,i),k} t^k`,
bilinearity of `Φ` gives `B = C^in G_K (C^in)ᵀ`, hence `det B = (det C^in)² Δ_K`. Since
`det C^in` is a `p`-adic unit, multiplying by its square does not change the Gauss valuation.

## Main definitions

* `Zeta5Irr.innerBasisGramMatrix`: the matrix `B` of the pairings `Φ(Ψ_{a,i}, Ψ_{c,j})`.

## Main results

* `Zeta5Irr.det_mul_mul_transpose_submatrix`: `det (A G Aᵀ) = (det A)² det G` for `A`
  rectangular with rows identified with columns.
* `Zeta5Irr.map_mul_gramMatrix_mul_transpose_apply`: `(A G_K Aᵀ)_{rs}` is the inner form of the
  rows of `A`, read as polynomials.
* `Zeta5Irr.vpG_map_det_map_mul_gramMatrix_mul_transpose`: a basis change with unit determinant
  does not move `v_p^G(Δ_K)`.
* `Zeta5Irr.sum_innerCoeffMatrix_mul_X_pow`: `Ψ_{a,i} = ∑_{k < h} C^in_{(a,i),k} t^k`.
* `Zeta5Irr.innerBasisGramMatrix_eq_mul`: `B = C^in G_K (C^in)ᵀ`.
* `Zeta5Irr.vpG_map_det_innerBasisGramMatrix`: `v_p^G(det B) = v_p^G(Δ_K)`.

## Implementation notes

* `B` has entries in `ℚ[X]`; its Gauss valuation is that of its image in `ℚ_p[X]`.
* `C^in` is rectangular in Lean, with rows indexed by the pairs `(a, i)` and columns by
  `Fin h`. The identity `B = C^in G_K (C^in)ᵀ` holds for all parameters; to take the
  determinant one identifies the two index types by a bijection `e`, and
  `det B = (det C^in)² Δ_K` holds for every such `e`.
* As in `Zeta5Irr.exists_isUnit_det_innerCoeffMatrix`, the hypothesis `K ∈ 40 ℤ_{>0}` is built
  into `K = 40 n` and the inequalities `K / M < p ≤ K / 3` are stated in `ℚ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- The matrix `B` of the inner pairings of the row polynomials:
`B_{(a,i),(c,j)} = Φ(Ψ_{a,i}, Ψ_{c,j})`, rows and columns indexed by the pairs `(a, i)` with
`0 ≤ a ≤ m°` and `0 ≤ i < L_a`. -/
@[zeta5irr "lem_in_basis_change"]
noncomputable def innerBasisGramMatrix (n p M : ℕ) :
    Matrix (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a))
      (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) ℚ[X] :=
  Matrix.of fun ai cj => innerForm n (rowPoly n p M ai.1 ai.2) (rowPoly n p M cj.1 cj.2)

/-- The entries of `B`: `B_{(a,i),(c,j)} = Φ(Ψ_{a,i}, Ψ_{c,j})`. -/
@[simp]
theorem innerBasisGramMatrix_apply (n p M : ℕ)
    (ai cj : Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) :
    innerBasisGramMatrix n p M ai cj =
      innerForm n (rowPoly n p M ai.1 ai.2) (rowPoly n p M cj.1 cj.2) :=
  rfl

/-- The entry `G_K(X)_{kl}` is `Φ(t^k, t^l)`. -/
theorem gramMatrix_apply_eq_innerForm (n : ℕ) (k l : Fin (matrixOrder n)) :
    gramMatrix n k l = innerForm n (X ^ (k : ℕ)) (X ^ (l : ℕ)) := by
  rw [gramMatrix_apply_eq, innerForm, mul_assoc, pow_add]

/-- If the rows of a rectangular matrix `A` are identified with its columns by a bijection `e`,
then `det (A G Aᵀ) = (det A)² det G`. -/
theorem det_mul_mul_transpose_submatrix {R ι κ : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ R) (G : Matrix κ κ R)
    (e : ι ≃ κ) :
    (A * G * A.transpose).det = (A.submatrix id e).det ^ 2 * G.det := by
  have h : A * G * A.transpose =
      A.submatrix id e * G.submatrix e e * (A.submatrix id e).transpose := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
  ring

/-- Conjugating `G_K` by a rational matrix `A` computes the inner form on the rows of `A`, read
as polynomials: `(A G_K Aᵀ)_{rs} = Φ(∑_k A_{rk} t^k, ∑_l A_{sl} t^l)`. -/
theorem map_mul_gramMatrix_mul_transpose_apply {ι : Type*} (n : ℕ)
    (A : Matrix ι (Fin (matrixOrder n)) ℚ) (r s : ι) :
    (A.map C * gramMatrix n * (A.map C).transpose) r s =
      innerForm n (∑ k : Fin (matrixOrder n), C (A r k) * X ^ (k : ℕ))
        (∑ l : Fin (matrixOrder n), C (A s l) * X ^ (l : ℕ)) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    gramMatrix_apply_eq_innerForm, innerForm, Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [show ∀ a b : ℚ, ∀ A B D : ℚ[X], D * (C a * A) * (C b * B) = C a * (C b * (D * A * B))
    from fun _ _ _ _ _ => by ring, rationalFunctional_C_mul, rationalFunctional_C_mul]
  ring

/-- **A unimodular basis change does not move the valuation.** Let `A` be a rational matrix with
`h = matrixOrder n` columns whose determinant, for an identification `e` of its rows with its
columns, is a `p`-adic unit. Then `v_p^G(det (A G_K Aᵀ)) = v_p^G(Δ_K)`. -/
theorem vpG_map_det_map_mul_gramMatrix_mul_transpose {p : ℕ} [Fact p.Prime] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {n : ℕ} (A : Matrix ι (Fin (matrixOrder n)) ℚ)
    (e : ι ≃ Fin (matrixOrder n)) (hA : ‖(((A.submatrix id e).det : ℚ) : ℚ_[p])‖ = 1) :
    vpG ((A.map C * gramMatrix n * (A.map C).transpose).det.map (Rat.castHom ℚ_[p])) =
      vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  rw [det_mul_mul_transpose_submatrix _ _ e, Matrix.submatrix_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← map_pow, ← gramDet]
  exact vpG_map_C_sq_mul_of_norm_eq_one hA _

/-- The integer version of `vpG_map_det_map_mul_gramMatrix_mul_transpose`: if `B` is an integer
matrix whose determinant (for an identification `e` of its rows with its columns) is a unit of
`ℤ_p`, then `v_p^G(det (B G_K Bᵀ)) = v_p^G(Δ_K)`. -/
theorem vpG_map_det_map_intCast_mul_gramMatrix_mul_transpose {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (B : Matrix ι (Fin (matrixOrder n)) ℤ)
    (e : ι ≃ Fin (matrixOrder n)) (hB : IsUnit (((B.submatrix id e).det : ℤ) : ℤ_[p])) :
    vpG ((B.map (Int.castRingHom ℚ[X]) * gramMatrix n *
        (B.map (Int.castRingHom ℚ[X])).transpose).det.map (Rat.castHom ℚ_[p])) =
      vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  have hB' : B.map (Int.castRingHom ℚ[X]) = (B.map (Int.castRingHom ℚ)).map C := by
    ext; simp
  rw [hB']
  refine vpG_map_det_map_mul_gramMatrix_mul_transpose _ e ?_
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using PadicInt.isUnit_iff.mp hB

variable {n p M : ℕ}

/-- In the range of parameters of §5.4, the row polynomial `Ψ_{a,i}` has degree less than `h`. -/
theorem natDegree_rowPoly_lt (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n) (hp : p.Prime)
    (hpl : (poleBound n : ℚ) / M < p) (hpu : (p : ℚ) ≤ poleBound n / 3)
    (a : Fin (mStar p + 1)) (i : Fin (rowPolyExponent n p M a)) :
    (rowPoly n p M a i).natDegree < matrixOrder n := by
  rw [natDegree_rowPoly, ← sum_rowPolyExponent hM hK hp hpl hpu,
    sum_eq_sum_sdiff_singleton_add (s := range (mStar p + 1)) (i := (a : ℕ)) (mem_range.2 a.2)]
  exact Nat.add_lt_add_left i.2 _

/-- In the range of parameters of §5.4, `Ψ_{a,i} = ∑_{k < h} C^in_{(a,i),k} t^k`. -/
theorem sum_innerCoeffMatrix_mul_X_pow (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hp : p.Prime) (hpl : (poleBound n : ℚ) / M < p) (hpu : (p : ℚ) ≤ poleBound n / 3)
    (ai : Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) :
    ∑ k : Fin (matrixOrder n), C (innerCoeffMatrix n p M ai k) * X ^ (k : ℕ) =
      rowPoly n p M ai.1 ai.2 := by
  conv_rhs => rw [as_sum_range' _ _ (natDegree_rowPoly_lt hM hK hp hpl hpu ai.1 ai.2)]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [C_mul_X_pow_eq_monomial]

/-- **Basis change for the inner form** (§5.4). In the range of parameters of §5.4,
`B = C^in G_K (C^in)ᵀ`. -/
theorem innerBasisGramMatrix_eq_mul (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hp : p.Prime) (hpl : (poleBound n : ℚ) / M < p) (hpu : (p : ℚ) ≤ poleBound n / 3) :
    innerBasisGramMatrix n p M =
      (innerCoeffMatrix n p M).map C * gramMatrix n *
        ((innerCoeffMatrix n p M).map C).transpose := by
  refine Matrix.ext fun ai cj => ?_
  rw [map_mul_gramMatrix_mul_transpose_apply, innerBasisGramMatrix_apply,
    sum_innerCoeffMatrix_mul_X_pow hM hK hp hpl hpu,
    sum_innerCoeffMatrix_mul_X_pow hM hK hp hpl hpu]

/-- **The basis change does not move the valuation** (§5.4). Let `M ≥ 40`, `K = 40 n ≥ 200 M²`
and let `p` be a prime with `K / M < p ≤ K / 3`. Then `v_p^G(det B) = v_p^G(Δ_K)`, where
`B_{(a,i),(c,j)} = Φ(Ψ_{a,i}, Ψ_{c,j})`. -/
@[zeta5irr "lem_in_basis_change"]
theorem vpG_map_det_innerBasisGramMatrix [Fact p.Prime] (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : (poleBound n : ℚ) / M < p)
    (hpu : (p : ℚ) ≤ poleBound n / 3) :
    vpG ((innerBasisGramMatrix n p M).det.map (Rat.castHom ℚ_[p])) =
      vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  have hp : p.Prime := Fact.out
  let e := Fintype.equivFinOfCardEq
    (card_innerCoeffMatrix_rows_eq_matrixOrder hM hK hp hpl hpu)
  rw [innerBasisGramMatrix_eq_mul hM hK hp hpl hpu]
  exact vpG_map_det_map_mul_gramMatrix_mul_transpose _ e
    (norm_det_innerCoeffMatrix_submatrix hM hK hpl hpu e)

end Zeta5Irr
