/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LocalEstimates.InClassesCoprime
public import Zeta5Irr.LocalEstimates.InCrtBasis
public import Zeta5Irr.LocalEstimates.OutV
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.RingHoms
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The separating basis is unimodular

Let `p` be an odd prime with `p ≤ K`. Then the outer coefficient matrix `C^out`, whose row
`(a, i)` is the coefficient vector of `P_a q_{a,i}`, is a square `(K - N) × (K - N)` matrix with
integer entries, and its determinant is a unit of `ℤ_p`.

Every far pole `N < j ≤ K` satisfies `j ≡ ±a (mod p)` for exactly one `0 ≤ a ≤ m°`, by the
partition of `{0, 1, …, p - 1}` into `{0}` and the pairs `{a, p - a}`, `1 ≤ a ≤ m°`. Hence the
class factors multiply to the tail polynomial, `∏_a Q_a = D_tail`, their degrees add up to
`K - N`, and `∏_{c ≠ a} Q_c = P_a`. For `a < a'` the factors `Q_a` and `Q_{a'}` are coprime over
`ℤ_p`: a root `-j²` of `Q_a` and a root `-j'²` of `Q_{a'}` differ by
`j'² - j² ≡ a'² - a² (mod p)`, a unit of `ℤ_p`. The local polynomials `q_{a,i}` are monic of
degree `i`, so the distributing basis lemma shows that the `P_a q_{a,i}` form a `ℤ_p`-basis of
the polynomials of degree less than `K - N`. The transpose of `C^out` is the change of basis
matrix from the monomial basis to this basis, so its determinant is a unit.

## Main results

* `Zeta5Irr.card_outerCoeffMatrix_rows_eq_matrixOrder`: for `N = 3 n`, `K = 40 n`, `C^out`
  has `h = 37 n` rows, so it is square.
* `Zeta5Irr.isUnit_det_outerCoeffMatrix`: the determinant of the integer matrix `C^out` is a
  unit of `ℤ_p`.
* `Zeta5Irr.isUnit_det_outerCoeffMatrix_padicInt`: the same for `C^out` over `ℤ_p`.
* `Zeta5Irr.prod_residuePoleProduct`, `Zeta5Irr.sum_card_residuePoleIndices`,
  `Zeta5Irr.prod_compl_residuePoleProduct`: `∏_a Q_a = D_tail`, `∑_a deg Q_a = K - N` and
  `∏_{c ≠ a} Q_c = P_a`.
* `Zeta5Irr.isCoprime_residuePoleProduct`: `Q_a` and `Q_{a'}` are coprime over `ℤ_p`.

## Implementation notes

* The source assumes `K ∈ 40 ℤ_{>0}`, `p ≥ 7`, `p ≤ K < 3 p`, `p² > 2 K`, `2 N < p` and
  `5 N ≤ 2 p - 2`. The argument uses only that `p` is an odd prime and that `p ≤ K` (the latter
  for the degrees of the local polynomials `q_{a,i}`, `a ≥ 1`), so the determinant statement is
  made for arbitrary `N`, `K`, `h` under these hypotheses alone. The squareness statement is
  given for the source's parameters `N = 3 n`, `K = 40 n`, `h = 37 n`; in general `C^out` has
  `K - N` rows (`Zeta5Irr.card_outerCoeffMatrix_rows`).
* The rows of `C^out` are indexed by pairs `(a, i)` and its columns by `Fin h`. To speak of its
  determinant one identifies the two index types by a bijection `e`; the statement is made for
  every such `e` (a different choice only changes the sign of the determinant). The existence
  of `e` forces `h = K - N`.
* The entries of `C^out` are integers by construction: the determinant statement is made for
  the matrix over `ℤ`, whose determinant is cast into `ℤ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8 (The outer range: the separating basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- For odd `p` and `0 ≤ a ≤ m°`, a natural number `j` satisfies `j ≡ ±a (mod p)` if and only
if `a` is the representative of the pair of classes `±j` in `[0, m°]`, namely `j mod p` when
this is at most `m°` and `p - (j mod p)` otherwise. -/
theorem natCast_eq_or_eq_neg_iff {p : ℕ} (hp : Odd p) {a : ℕ} (ha : a ≤ mStar p) (j : ℕ) :
    ((j : ZMod p) = ((a : ℤ) : ZMod p) ∨ (j : ZMod p) = -((a : ℤ) : ZMod p)) ↔
      (if j % p ≤ mStar p then j % p else p - j % p) = a := by
  have h2 := two_mul_mStar_add_one hp
  have hp0 : 0 < p := by omega
  have : NeZero p := ⟨by omega⟩
  have hjp := Nat.mod_lt j hp0
  rw [Int.cast_natCast]
  have hv : ∀ x y : ZMod p, x = y ↔ x.val = y.val := fun x y => ZMod.val_injective p |>.eq_iff.symm
  rw [hv, hv, ZMod.neg_val, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (a := a)
    (by omega)]
  have : ((a : ZMod p) = 0) ↔ a = 0 := by
    rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero]
  split_ifs <;> simp_all <;> omega

/-- For odd `p`, the far poles `N < j ≤ K` in the classes `±a`, `0 ≤ a ≤ m°`, are the fibre over
`a` of the map sending `j` to its representative in `[0, m°]`. -/
theorem residuePoleIndices_eq_filter {p : ℕ} (hp : Odd p) {a : ℕ} (ha : a ≤ mStar p)
    (N K : ℕ) : residuePoleIndices p a N K =
      (Ioc N K).filter fun j ↦ (if j % p ≤ mStar p then j % p else p - j % p) = a := by
  ext j
  rw [mem_residuePoleIndices, mem_filter, mem_Ioc, natCast_eq_or_eq_neg_iff hp ha]

/-- The representative in `[0, m°]` of the classes `±j` lies in `[0, m°]`. -/
theorem mapsTo_residueRep {p : ℕ} (hp : Odd p) (N K : ℕ) :
    Set.MapsTo (fun j ↦ if j % p ≤ mStar p then j % p else p - j % p) (Ioc N K)
      (range (mStar p + 1)) := by
  intro j _
  have h2 := two_mul_mStar_add_one hp
  have := Nat.mod_lt j (show 0 < p by omega)
  simp only [coe_range, Set.mem_Iio]
  split_ifs <;> omega

/-- For odd `p`, the class counts add up to the number of far poles:
`∑_{0 ≤ a ≤ m°} deg Q_a = K - N`. -/
theorem sum_card_residuePoleIndices {p : ℕ} (hp : Odd p) (N K : ℕ) :
    ∑ a ∈ range (mStar p + 1), #(residuePoleIndices p a N K) = K - N := by
  rw [← Nat.card_Ioc N K, card_eq_sum_card_fiberwise (mapsTo_residueRep hp N K)]
  refine sum_congr rfl fun a ha ↦ ?_
  rw [residuePoleIndices_eq_filter hp (by simpa [Nat.lt_succ_iff] using ha)]

/-- For odd `p`, the residue-class pole products factor the tail polynomial:
`∏_{0 ≤ a ≤ m°} Q_a = D_tail`. -/
theorem prod_residuePoleProduct {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (N K : ℕ) :
    ∏ a ∈ range (mStar p + 1), residuePoleProduct R p a N K = dTail R N K := by
  rw [dTail, Finset.Icc_add_one_left_eq_Ioc, ← prod_fiberwise_of_maps_to (mapsTo_residueRep hp N K)]
  refine prod_congr rfl fun a ha ↦ ?_
  rw [residuePoleProduct, residuePoleIndices_eq_filter hp (by simpa [Nat.lt_succ_iff] using ha)]

/-- For odd `p` and `0 ≤ a ≤ m°`, the product of the class factors `Q_c`, `c ≠ a`, is the
complementary class factor: `∏_{c ≠ a} Q_c = P_a`. -/
theorem prod_compl_residuePoleProduct {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    (hp : Odd p) (N K : ℕ) (a : Fin (mStar p + 1)) :
    ∏ c ∈ {a}ᶜ, residuePoleProduct R p (c : ℕ) N K = complClassFactor R p (a : ℕ) N K := by
  have h1 : residuePoleProduct R p (a : ℕ) N K * ∏ c ∈ {a}ᶜ, residuePoleProduct R p (c : ℕ) N K =
      dTail R N K := by
    rw [← prod_residuePoleProduct hp, ← Fin.prod_univ_eq_prod_range
      (fun c ↦ residuePoleProduct R p (c : ℕ) N K), ← prod_mul_prod_compl {a}, prod_singleton]
  exact mul_left_cancel₀ (residuePoleProduct_monic p _ N K).ne_zero
    (h1.trans (prod_mul_complClassFactor p _ N K).symm)

/-- A `p`-adic integer is a unit if and only if its reduction modulo `p` is nonzero. -/
theorem PadicInt.isUnit_iff_toZMod_ne_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} :
    IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [ne_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- For an odd prime `p` and `0 ≤ a < a' ≤ m°`, the class factors `Q_a` and `Q_{a'}` are
coprime over `ℤ_p`: every root `-j²` of the first differs from every root `-j'²` of the second
by `j'² - j² ≡ a'² - a² (mod p)`, a unit of `ℤ_p`. -/
theorem isCoprime_residuePoleProduct {p : ℕ} [Fact p.Prime] (hp : Odd p) (N K : ℕ) {a a' : ℕ}
    (haa' : a < a') (ha' : a' ≤ mStar p) :
    IsCoprime (residuePoleProduct ℤ_[p] p a N K) (residuePoleProduct ℤ_[p] p a' N K) := by
  have hu := isUnit_sq_sub_sq_of_lt_of_le_mStar hp haa' ha'
  rw [PadicInt.isUnit_iff_toZMod_ne_zero] at hu
  refine IsCoprime.prod_left fun j hj ↦ IsCoprime.prod_right fun j' hj' ↦ ?_
  rw [mem_residuePoleIndices, Int.cast_natCast] at hj hj'
  have hsq : ∀ {i b : ℕ}, ((i : ZMod p) = b ∨ (i : ZMod p) = -(b : ZMod p)) →
      (i : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := by
    rintro i b (h | h) <;> simp [h]
  have := isCoprime_X_sub_C_of_isUnit_sub (R := ℤ_[p]) (a := -(j : ℤ_[p]) ^ 2)
    (b := -(j' : ℤ_[p]) ^ 2) (by
      rw [map_sub, map_pow, map_pow, map_natCast, map_natCast] at hu
      rw [PadicInt.isUnit_iff_toZMod_ne_zero, map_sub, map_neg, map_neg, map_pow, map_pow,
        map_natCast, map_natCast, hsq hj.2, hsq hj'.2]
      convert hu using 1
      ring)
  simpa [sub_eq_add_neg] using this

/-- For odd `p`, the matrix `C^out` has `K - N` rows. -/
theorem card_outerCoeffMatrix_rows {p : ℕ} (hp : Odd p) (N K : ℕ) :
    Fintype.card (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) = K - N := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun a ↦ #(residuePoleIndices p a N K)),
    sum_card_residuePoleIndices hp]

/-- **The separating basis is unimodular**, squareness (§5.8). For an odd prime `p` and
`N = 3 n`, `K = 40 n`, the matrix `C^out` has `h = 37 n` rows, so it is square. -/
@[zeta5irr "lem_out_unimodular"]
theorem card_outerCoeffMatrix_rows_eq_matrixOrder {p : ℕ} (hp : Odd p) (n : ℕ) :
    Fintype.card (Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) = matrixOrder n := by
  rw [card_outerCoeffMatrix_rows hp, poleBound, innerDegree, matrixOrder]
  omega

/-- For an odd prime `p ≤ K` and `0 ≤ a ≤ m°`, the local polynomial `q_{a,i}` has degree `i`. -/
theorem natDegree_outerLocalPoly {p K : ℕ} [Fact p.Prime] (hp : Odd p) (hpK : p ≤ K) {a : ℕ}
    (ha : a ≤ mStar p) (i : ℕ) : (outerLocalPoly ℤ_[p] p K a i).natDegree = i := by
  by_cases h0 : a = 0
  · rw [h0, Nat.cast_zero, outerLocalPoly_zero, natDegree_multiplePoleProduct]
  · rw [outerLocalPoly_of_ne_zero (by exact_mod_cast h0)]
    exact natDegree_outerBasis hp (by omega) (by exact_mod_cast ha) hpK i

/-- For an odd prime `p`, the reductions of the residue-class pole products `Q_c`,
`0 ≤ c ≤ m°`, over the residue field of `ℤ_p` are pairwise coprime. -/
theorem pairwise_isCoprime_map_residue_residuePoleProduct {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (N K : ℕ) :
    Pairwise fun k k' : Fin (mStar p + 1) ↦
      IsCoprime ((residuePoleProduct ℤ_[p] p (k : ℕ) N K).map (IsLocalRing.residue ℤ_[p]))
        ((residuePoleProduct ℤ_[p] p (k' : ℕ) N K).map (IsLocalRing.residue ℤ_[p])) := by
  intro k k' hkk'
  rcases hkk'.lt_or_gt with hlt | hlt
  · exact (isCoprime_residuePoleProduct hp N K hlt (Nat.lt_succ_iff.mp k'.2)).map
      (mapRingHom (IsLocalRing.residue ℤ_[p]))
  · exact ((isCoprime_residuePoleProduct hp N K hlt (Nat.lt_succ_iff.mp k.2)).map
      (mapRingHom (IsLocalRing.residue ℤ_[p]))).symm

/-- For an odd prime `p ≤ K` and any identification `e` of the rows of `C^out` with its `h`
columns, the determinant of the square matrix `C^out` over `ℤ_p` is a unit. -/
theorem isUnit_det_outerCoeffMatrix_padicInt {p N K h : ℕ} [Fact p.Prime] (hp : Odd p)
    (hpK : p ≤ K)
    (e : (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) ≃ Fin h) :
    IsUnit ((outerCoeffMatrix ℤ_[p] p N K h).submatrix id e).det := by
  have hM : (outerCoeffMatrix ℤ_[p] p N K h).submatrix id e = Matrix.of fun ai aj ↦
      ((∏ k' ∈ ({ai.1}ᶜ : Finset (Fin (mStar p + 1))),
          residuePoleProduct ℤ_[p] p (k' : ℕ) N K) *
        outerLocalPoly ℤ_[p] p K (ai.1 : ℕ) (ai.2 : ℕ)).coeff (e aj) := by
    ext ai aj
    rw [Matrix.submatrix_apply, id, outerCoeffMatrix_apply, Matrix.of_apply,
      prod_compl_residuePoleProduct hp]
  rw [hM]
  exact isUnit_det_coeff_prod_compl_mul (fun _ ↦ residuePoleProduct_monic p _ N K)
    (fun _ ↦ natDegree_residuePoleProduct p _ N K)
    (pairwise_isCoprime_map_residue_residuePoleProduct hp N K)
    (fun k i ↦ outerLocalPoly ℤ_[p] p K (k : ℕ) i) (fun _ _ ↦ outerLocalPoly_monic p K _ _)
    (fun k i ↦ natDegree_outerLocalPoly hp hpK (Nat.lt_succ_iff.mp k.2) i) e

/-- **The separating basis is unimodular** (§5.8). For an odd prime `p ≤ K` and any
identification `e` of the rows of `C^out` with its `h` columns, the square matrix `C^out` has
integer entries and its determinant is a unit of `ℤ_p`. -/
@[zeta5irr "lem_out_unimodular"]
theorem isUnit_det_outerCoeffMatrix {p N K h : ℕ} [Fact p.Prime] (hp : Odd p) (hpK : p ≤ K)
    (e : (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) ≃ Fin h) :
    IsUnit ((((outerCoeffMatrix ℤ p N K h).submatrix id e).det : ℤ) : ℤ_[p]) := by
  have := isUnit_det_outerCoeffMatrix_padicInt hp hpK e
  rwa [← map_intCast_outerCoeffMatrix, Matrix.submatrix_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, eq_intCast] at this

end Zeta5Irr
