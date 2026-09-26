/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutQ
public import Zeta5Irr.LocalEstimates.OutP
public import Zeta5Irr.LocalEstimates.OutQLower
public import Zeta5Irr.LocalEstimates.OutQ0
public import Mathlib.Data.Finset.Slice

/-!
# The outer coefficient matrix `C^out`

For a prime `p`, the separating basis of the outer range consists of the polynomials
`P_a q_{a,i}` for `0 ≤ a ≤ m°` and `0 ≤ i < deg Q_a`, where `Q_a` and `P_a` are the class
factor and the complementary class factor, `q_{0,i} = ∏_{k=1}^{i} (t + (k p)²)` and, for
`a ≥ 1`, `q_{a,i}` is the ordinary local polynomial. The outer coefficient matrix `C^out` has
rows indexed by the pairs `(a, i)`, columns indexed by `0 ≤ k < h`, and entry at `((a, i), k)`
the coefficient of `t^k` in `P_a q_{a,i}`. Whenever `deg (P_a q_{a,i}) < h`, the row `(a, i)`
of `C^out` is therefore the coefficient vector of `P_a q_{a,i}`.

## Main definitions

* `Zeta5Irr.outerLocalPoly`: the local polynomial `q_{a,i}`, for `a = 0` and `a ≥ 1` alike.
* `Zeta5Irr.outerCoeffMatrix`: the matrix `C^out`.

## Main results

* `Zeta5Irr.outerCoeffMatrix_apply`: the entry at `((a, i), k)` is the coefficient of `t^k`
  in `P_a q_{a,i}`.
* `Zeta5Irr.map_outerCoeffMatrix`: `C^out` commutes with ring homomorphisms; in particular
  the matrix over any ring is the image of the integer matrix.
* `Zeta5Irr.sum_outerCoeffMatrix_mul_X_pow`: if `deg (P_a q_{a,i}) < h` then
  `P_a q_{a,i} = ∑_{k < h} C^out_{(a,i),k} t^k`.
* `Zeta5Irr.outerLocalPoly_monic`: every `q_{a,i}` is monic.

## Implementation notes

* The two families `q_{0,i}` and `q_{a,i}` (`a ≥ 1`) of the source are packaged into the single
  function `outerLocalPoly`, which is `q_{0,i}` at `a = 0` and `q_{a,i}` otherwise.
* The row index is the dependent pair type `Σ a : Fin (m° + 1), Fin (ℓ a)`, where `ℓ a` is the
  number of `N < j ≤ K` with `j ≡ ±a (mod p)`. By `Zeta5Irr.natDegree_residuePoleProduct` this
  is `deg Q_a` over every nontrivial ring; counting indices makes the row type independent of the
  coefficient ring.
* The source fixes `N = 3n`, `K = 40n` and `h = 37n`; here `N`, `K`, `h` are arbitrary natural
  numbers, and `p` is an arbitrary natural number, primality being needed only by the consumers.
  The matrix is defined over any commutative ring `R` (the source uses `ℤ`, `ℚ` and `ℤ_p`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable (R : Type*) [CommRing R]

/-- The local polynomial `q_{a,i}` of the separating basis of the outer range: the zero-class
polynomial `q_{0,i} = ∏_{k=1}^{i} (X + (k p)²)` when `a = 0`, and the ordinary local polynomial
`q_{a,i}` of `Zeta5Irr.outerBasis` otherwise. -/
noncomputable def outerLocalPoly (p K : ℕ) (a : ℤ) (i : ℕ) : R[X] :=
  if a = 0 then multiplePoleProduct R p i else outerBasis R p K a i

/-- The outer coefficient matrix `C^out`: rows are indexed by pairs `(a, i)` with
`0 ≤ a ≤ m°` and `0 ≤ i < deg Q_a`, columns by `0 ≤ k < h`, and the entry at `((a, i), k)` is
the coefficient of `t^k` in `P_a q_{a,i}`. -/
@[zeta5irr "def_out_V"]
noncomputable def outerCoeffMatrix (p N K h : ℕ) :
    Matrix (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) (Fin h) R :=
  fun ai k ↦
    (complClassFactor R p (ai.1 : ℕ) N K * outerLocalPoly R p K (ai.1 : ℕ) ai.2).coeff k

variable {R}

/-- At `a = 0` the local polynomial is `q_{0,i}`. -/
@[simp]
theorem outerLocalPoly_zero (p K i : ℕ) :
    outerLocalPoly R p K 0 i = multiplePoleProduct R p i := by
  simp [outerLocalPoly]

/-- At `a ≠ 0` the local polynomial is the ordinary `q_{a,i}`. -/
theorem outerLocalPoly_of_ne_zero {p K : ℕ} {a : ℤ} (ha : a ≠ 0) (i : ℕ) :
    outerLocalPoly R p K a i = outerBasis R p K a i := by
  simp [outerLocalPoly, ha]

/-- Every local polynomial `q_{a,i}` is monic. -/
theorem outerLocalPoly_monic (p K : ℕ) (a : ℤ) (i : ℕ) : (outerLocalPoly R p K a i).Monic := by
  unfold outerLocalPoly
  split_ifs
  · exact multiplePoleProduct_monic p i
  · exact outerBasis_monic p K a i

/-- The local polynomials commute with ring homomorphisms. -/
theorem map_outerLocalPoly {S : Type*} [CommRing S] (f : R →+* S) (p K : ℕ) (a : ℤ) (i : ℕ) :
    (outerLocalPoly R p K a i).map f = outerLocalPoly S p K a i := by
  unfold outerLocalPoly
  split_ifs
  · exact map_multiplePoleProduct f p i
  · exact map_outerBasis f p K a i

/-- The entry of `C^out` at `((a, i), k)` is the coefficient of `t^k` in `P_a q_{a,i}`. -/
theorem outerCoeffMatrix_apply (p N K h : ℕ)
    (ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) (k : Fin h) :
    outerCoeffMatrix R p N K h ai k =
      (complClassFactor R p (ai.1 : ℕ) N K * outerLocalPoly R p K (ai.1 : ℕ) ai.2).coeff k :=
  rfl

/-- The complementary class factor commutes with ring homomorphisms. -/
theorem map_complClassFactor {S : Type*} [CommRing S] (f : R →+* S) (p : ℕ) (a : ℤ)
    (N K : ℕ) : (complClassFactor R p a N K).map f = complClassFactor S p a N K := by
  simp [complClassFactor, Polynomial.map_prod]

/-- The outer coefficient matrix commutes with ring homomorphisms. -/
theorem map_outerCoeffMatrix {S : Type*} [CommRing S] (f : R →+* S) (p N K h : ℕ) :
    (outerCoeffMatrix R p N K h).map f = outerCoeffMatrix S p N K h := by
  ext ai k
  rw [Matrix.map_apply, outerCoeffMatrix_apply, outerCoeffMatrix_apply, ← coeff_map,
    Polynomial.map_mul, map_complClassFactor, map_outerLocalPoly]

/-- Over any commutative ring, `C^out` is the image of the integer matrix `C^out`. -/
theorem map_intCast_outerCoeffMatrix (p N K h : ℕ) :
    (outerCoeffMatrix ℤ p N K h).map (Int.castRingHom R) = outerCoeffMatrix R p N K h :=
  map_outerCoeffMatrix _ p N K h

/-- If `deg (P_a q_{a,i}) < h`, the row `(a, i)` of `C^out` is the coefficient vector of
`P_a q_{a,i}`: `P_a q_{a,i} = ∑_{k < h} C^out_{(a,i),k} t^k`. -/
theorem sum_outerCoeffMatrix_mul_X_pow {p N K h : ℕ}
    (ai : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K))
    (hdeg : (complClassFactor R p (ai.1 : ℕ) N K *
      outerLocalPoly R p K (ai.1 : ℕ) ai.2).natDegree < h) :
    ∑ k : Fin h, C (outerCoeffMatrix R p N K h ai k) * X ^ (k : ℕ) =
      complClassFactor R p (ai.1 : ℕ) N K * outerLocalPoly R p K (ai.1 : ℕ) ai.2 := by
  simp_rw [outerCoeffMatrix_apply, C_mul_X_pow_eq_monomial]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ monomial k (coeff _ k)), ← as_sum_range' _ _ hdeg]

end Zeta5Irr
