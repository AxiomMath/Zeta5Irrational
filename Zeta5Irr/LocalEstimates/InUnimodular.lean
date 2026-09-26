/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InU
public import Zeta5Irr.LocalEstimates.LaNonneg
public import Zeta5Irr.LocalEstimates.InLaSum
public import Zeta5Irr.LocalEstimates.InClassesCoprime
public import Zeta5Irr.LocalEstimates.InCrtBasis

/-!
# The row polynomials are unimodular

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²` and let `p` be a prime with `K / M < p ≤ K / 3`. Then the
coefficient matrix `C^in` of the row polynomials `Ψ_{a,i}` is a square `h × h` matrix with
entries in `ℤ_p`, and its determinant is a unit of `ℤ_p`.

The number of rows is `L₀ + ∑_{a ≥ 1} L_a = h`, since every `L_a` is nonnegative. The factors
`Πₐ = (t + a²)^{L_a}`, `0 ≤ a ≤ m°`, are monic and pairwise coprime over `ℤ_p`, because
`(t + a'²) - (t + a²) = a'² - a²` is a unit of `ℤ_p`; hence their reductions modulo `p` are
pairwise coprime. The distributing basis lemma applied to `Πₐ` and `q_{a,i} = (t + a²)^i`
shows that the `Ψ_{a,i} = (∏_{c ≠ a} Π_c) q_{a,i}` form a `ℤ_p`-basis of the polynomials of
degree less than `h`. The transpose of `C^in` is the change of basis matrix from the monomial
basis `1, t, …, t^{h-1}` to this basis, so its determinant is a unit.

## Main results

* `Zeta5Irr.card_innerCoeffMatrix_rows_eq_matrixOrder`: `C^in` has `h` rows, so it is square.
* `Zeta5Irr.exists_isUnit_det_innerCoeffMatrix`: `C^in` has entries in `ℤ_p` and
  `det C^in ∈ ℤ_p^×`.
* `Zeta5Irr.norm_det_innerCoeffMatrix_submatrix`: `‖det C^in‖_p = 1`.

## Implementation notes

* `Zeta5Irr.innerCoeffMatrix` has rational entries, rows indexed by the pairs `(a, i)` and
  columns by `Fin h`. To speak of its determinant one identifies the two index types by a
  bijection `e`; the statement is made for every such `e` (a different choice only changes the
  sign of the determinant). "Entries in `ℤ_p`" is expressed by a matrix `A` over `ℤ_[p]` whose
  image in `ℚ_[p]` is the image of `C^in`.
* The hypothesis `K ∈ 40 ℤ_{>0}` is built into the parametrisation `K = 40 n`, and the
  hypotheses `K / M < p ≤ K / 3` are stated in `ℚ`, as in `Zeta5Irr.two_le_innerClassDim`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- If `M ≥ 40`, `K = 40 n ≥ 200 M²` and `K / M < p`, then `8000 < p`. -/
theorem lt_of_poleBound_div_lt {n p M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hpl : (poleBound n : ℚ) / M < p) : 8000 < p := by
  have hM' : (40 : ℚ) ≤ M := by exact_mod_cast hM
  have hK' : (200 : ℚ) * M ^ 2 ≤ poleBound n := by exact_mod_cast hK
  have hMpos : (0 : ℚ) < M := by linarith
  have : (200 : ℚ) * M ≤ poleBound n / M := by
    rw [le_div_iff₀ hMpos]; nlinarith
  have : (8000 : ℚ) < p := by nlinarith
  exact_mod_cast this

/-- In the range of parameters of §5.4, the exponents of the factors `(t + c²)` add up to `h`:
`∑_{0 ≤ c ≤ m°} L_c = h`. -/
theorem sum_rowPolyExponent {n p M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hp : p.Prime) (hpl : (poleBound n : ℚ) / M < p) (hpu : (p : ℚ) ≤ poleBound n / 3) :
    ∑ c ∈ range (mStar p + 1), rowPolyExponent n p M c = matrixOrder n := by
  have h8 := lt_of_poleBound_div_lt hM hK hpl
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsum := zeroClassDim_add_sum_innerClassDim n M hodd (by omega)
  have hr : range (mStar p + 1) = insert 0 (Icc 1 (mStar p)) := by
    ext; simp; omega
  rw [hr, sum_insert (by simp), rowPolyExponent_zero]
  have : ∑ a ∈ Icc 1 (mStar p), (rowPolyExponent n p M a : ℤ) =
      ∑ a ∈ Icc 1 (mStar p), innerClassDim n p M a := by
    refine sum_congr rfl fun a ha => ?_
    rw [mem_Icc] at ha
    exact cast_rowPolyExponent_of_ne_zero n p M (by omega)
      ((two_le_innerClassDim hM hK hpl hpu ha.1 ha.2).trans' (by norm_num))
  zify
  rw [this]
  push_cast at hsum
  linarith

/-- The image of the row polynomial `Ψ_{a,i}` in `ℚ_[p][t]` is the image of the polynomial
`(∏_{c ≠ a} (t + c²)^{L_c}) (t + a²)^i` over `ℤ_[p]`; in particular `Ψ_{a,i}` has coefficients
in `ℤ_p`. -/
theorem map_rowPoly_eq {p : ℕ} [Fact p.Prime] (n M : ℕ) (a : Fin (mStar p + 1)) (i : ℕ) :
    (rowPoly n p M a i).map (Rat.castHom ℚ_[p]) =
      ((∏ k ∈ {a}ᶜ, (X + C ((k : ℤ_[p]) ^ 2)) ^ rowPolyExponent n p M k) *
        (X + C ((a : ℤ_[p]) ^ 2)) ^ i).map PadicInt.Coe.ringHom := by
  simp only [rowPoly_def, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  congr 1
  have : range (mStar p + 1) \ {(a : ℕ)} = ({a}ᶜ : Finset (Fin (mStar p + 1))).map
      Fin.valEmbedding := by
    ext c
    simp only [mem_sdiff, mem_range, mem_singleton, mem_map, mem_compl, Fin.valEmbedding_apply]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨⟨c, h₁⟩, fun h => h₂ (by simp [← h]), rfl⟩,
      fun ⟨k, hk, hc⟩ => hc ▸ ⟨k.2, fun h => hk (Fin.ext h)⟩⟩
  rw [this, prod_map]
  exact prod_congr rfl fun k _ => by simp

/-- **The row polynomials are unimodular**, squareness (§5.4). For `M ≥ 40`, `K = 40 n ≥ 200 M²`
and a prime `p` with `K / M < p ≤ K / 3`, the matrix `C^in` has `h` rows, so it is square. -/
@[zeta5irr "lem_in_unimodular"]
theorem card_innerCoeffMatrix_rows_eq_matrixOrder {n p M : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : p.Prime) (hpl : (poleBound n : ℚ) / M < p)
    (hpu : (p : ℚ) ≤ poleBound n / 3) :
    Fintype.card (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) = matrixOrder n := by
  rw [card_innerCoeffMatrix_rows, sum_rowPolyExponent hM hK hp hpl hpu]

variable {n p M : ℕ} [Fact p.Prime]

/-- For odd `p` and `c < c' ≤ m*`, powers of `t + c²` and `t + c'²` are coprime over `ℤ_p`. -/
theorem isCoprime_X_add_C_sq_pow_of_lt (hodd : Odd p) {c c' : Fin (mStar p + 1)} (h : c < c')
    (m m' : ℕ) :
    IsCoprime ((X + C ((c : ℤ_[p]) ^ 2)) ^ m) ((X + C ((c' : ℤ_[p]) ^ 2)) ^ m') := by
  refine IsCoprime.pow ?_
  have hu := isUnit_sq_sub_sq_of_lt_of_le_mStar (p := p) hodd h (Nat.lt_succ_iff.mp c'.2)
  simpa only [sub_eq_add_neg, ← map_neg, neg_neg] using isCoprime_X_sub_C_of_isUnit_sub (R := ℤ_[p])
    (a := -(c : ℤ_[p]) ^ 2) (b := -(c' : ℤ_[p]) ^ 2) (by convert hu using 1; ring)

/-- **The row polynomials are unimodular** (§5.4). For `M ≥ 40`, `K = 40 n ≥ 200 M²` and a
prime `p` with `K / M < p ≤ K / 3`, and any identification `e` of the rows of `C^in` with its
columns, the square matrix `C^in` has entries in `ℤ_p` and its determinant is a unit of `ℤ_p`:
there is a matrix `A` over `ℤ_[p]` with `IsUnit (det A)` whose image in `ℚ_[p]` is `C^in`. -/
@[zeta5irr "lem_in_unimodular"]
theorem exists_isUnit_det_innerCoeffMatrix (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hpl : (poleBound n : ℚ) / M < p) (hpu : (p : ℚ) ≤ poleBound n / 3)
    (e : (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) ≃ Fin (matrixOrder n)) :
    ∃ A : Matrix (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a))
        (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) ℤ_[p],
      IsUnit A.det ∧ ∀ ai aj, (A ai aj : ℚ_[p]) = innerCoeffMatrix n p M ai (e aj) := by
  -- The upper bound `hpu : p ≤ K / 3` of the source is not needed: the identification `e`
  -- already forces `C^in` to be square.
  have _ := hpu
  have hp : p.Prime := Fact.out
  have h8 := lt_of_poleBound_div_lt hM hK hpl
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hdeg (c : Fin (mStar p + 1)) (m : ℕ) : ((X + C ((c : ℤ_[p]) ^ 2)) ^ m).natDegree = m := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have hcop : Pairwise fun k k' : Fin (mStar p + 1) =>
      IsCoprime (((X + C ((k : ℤ_[p]) ^ 2)) ^ rowPolyExponent n p M k).map
          (IsLocalRing.residue ℤ_[p]))
        (((X + C ((k' : ℤ_[p]) ^ 2)) ^ rowPolyExponent n p M k').map
          (IsLocalRing.residue ℤ_[p])) := by
    intro k k' hkk'
    rcases lt_or_gt_of_ne hkk' with h | h
    · exact (isCoprime_X_add_C_sq_pow_of_lt hodd h _ _).map
        (mapRingHom (IsLocalRing.residue ℤ_[p]))
    · exact ((isCoprime_X_add_C_sq_pow_of_lt hodd h _ _).map
        (mapRingHom (IsLocalRing.residue ℤ_[p]))).symm
  refine ⟨_, isUnit_det_coeff_prod_compl_mul (fun _ => (monic_X_add_C _).pow _)
    (fun c => hdeg c _) hcop (fun k i => (X + C ((k : ℤ_[p]) ^ 2)) ^ i)
    (fun _ _ => (monic_X_add_C _).pow _) hdeg e, fun ai aj => ?_⟩
  have := congrArg (fun f => f.coeff (e aj)) (map_rowPoly_eq n M ai.1 ai.2)
  simp only [coeff_map] at this
  rw [Matrix.of_apply, innerCoeffMatrix_apply]
  exact this.symm

/-- The determinant of the square matrix `C^in` has `p`-adic norm `1`. -/
theorem norm_det_innerCoeffMatrix_submatrix (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : (poleBound n : ℚ) / M < p)
    (hpu : (p : ℚ) ≤ poleBound n / 3)
    (e : (Σ a : Fin (mStar p + 1), Fin (rowPolyExponent n p M a)) ≃ Fin (matrixOrder n)) :
    ‖((((innerCoeffMatrix n p M).submatrix id e).det : ℚ) : ℚ_[p])‖ = 1 := by
  obtain ⟨A, hA, hAe⟩ := exists_isUnit_det_innerCoeffMatrix hM hK hpl hpu e
  have : (A.map PadicInt.Coe.ringHom) =
      ((innerCoeffMatrix n p M).submatrix id e).map (Rat.castHom ℚ_[p]) := by
    ext ai aj
    exact hAe ai aj
  have hdet := congrArg Matrix.det this
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← RingHom.map_det] at hdet
  change ‖Rat.castHom ℚ_[p] _‖ = 1
  rw [← hdet]
  exact PadicInt.isUnit_iff.mp hA

end Zeta5Irr
