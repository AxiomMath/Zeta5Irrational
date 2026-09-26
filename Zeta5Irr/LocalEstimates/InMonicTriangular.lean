/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Triangular families of polynomials are bases of `R[X]_n`

Let `R` be a commutative ring and `n` a natural number. If `q₀, …, q_{n-1}` are polynomials over
`R` such that `qᵢ` has degree at most `i` and its coefficient of `Xⁱ` is a unit, then
`q₀, …, q_{n-1}` is a basis of the `R`-module `R[X]_n` of polynomials of degree less than `n`.
In particular this holds when each `qᵢ` is monic of degree exactly `i`.

The proof is the determinant argument: the matrix of the family in the monomial basis
`1, X, …, X^{n-1}` is upper triangular with unit diagonal, so its determinant is a unit.

## Main definitions

* `Polynomial.degreeLT.basisOfTriangular`: the basis of `R[X]_n` given by a triangular family
  with unit diagonal coefficients.

## Main results

* `Polynomial.degreeLT.isUnit_det_of_triangular`: the determinant of such a family with respect
  to the monomial basis is a unit.
* `Polynomial.degreeLT.coe_basisOfTriangular`: the basis vectors are the given polynomials.
* `Zeta5Irr.exists_basis_degreeLT_of_monic`: a family `qᵢ` of monic polynomials with
  `deg qᵢ = i` for `i < d` is a basis of the polynomials of degree less than `d`.

## Implementation notes

* The source works over `ℤ_p`; the statement holds over any commutative ring and is stated so.
* The hypothesis "monic of degree exactly `i`" is weakened in the general construction to
  "degree at most `i` with unit coefficient of `Xⁱ`", which is all the argument uses.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4: the inner range, the distributing basis.
-/

@[expose] public section

open Module

namespace Polynomial.degreeLT

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A family `qᵢ` in `R[X]_n` with `deg qᵢ ≤ i` and unit coefficient of `Xⁱ` has unit
determinant with respect to the monomial basis. -/
theorem isUnit_det_of_triangular (q : Fin n → R[X]_n)
    (hdeg : ∀ i, (q i : R[X]).degree ≤ (i : ℕ)) (hunit : ∀ i, IsUnit ((q i : R[X]).coeff i)) :
    IsUnit ((basis R n).det q) := by
  rw [Basis.det_apply, Matrix.det_of_isUpperTriangular]
  · refine IsUnit.prod_univ_iff.mpr fun i ↦ ?_
    simpa [Basis.toMatrix_apply] using hunit i
  · intro i j hji
    rw [Basis.toMatrix_apply, basis_repr]
    exact coeff_eq_zero_of_degree_lt <| (hdeg j).trans_lt <| by exact_mod_cast hji

/-- The basis of `R[X]_n` given by a family `qᵢ` with `deg qᵢ ≤ i` and unit coefficient
of `Xⁱ`. -/
noncomputable def basisOfTriangular (q : Fin n → R[X]_n)
    (hdeg : ∀ i, (q i : R[X]).degree ≤ (i : ℕ)) (hunit : ∀ i, IsUnit ((q i : R[X]).coeff i)) :
    Basis (Fin n) R R[X]_n :=
  have h := (basis R n).is_basis_iff_det.mpr (isUnit_det_of_triangular q hdeg hunit)
  Basis.mk h.1 h.2.ge

/-- The `i`-th vector of `basisOfTriangular q` is `qᵢ`. -/
@[simp]
theorem basisOfTriangular_apply (q : Fin n → R[X]_n)
    (hdeg : ∀ i, (q i : R[X]).degree ≤ (i : ℕ)) (hunit : ∀ i, IsUnit ((q i : R[X]).coeff i))
    (i : Fin n) : basisOfTriangular q hdeg hunit i = q i :=
  by simp [basisOfTriangular]

/-- The basis vectors of `basisOfTriangular q` are the polynomials `qᵢ`. -/
theorem coe_basisOfTriangular (q : Fin n → R[X]_n)
    (hdeg : ∀ i, (q i : R[X]).degree ≤ (i : ℕ)) (hunit : ∀ i, IsUnit ((q i : R[X]).coeff i)) :
    ⇑(basisOfTriangular q hdeg hunit) = q :=
  _root_.funext fun i ↦ basisOfTriangular_apply q hdeg hunit i

end Polynomial.degreeLT

namespace Zeta5Irr

open Polynomial

/-- If `qᵢ` is monic of degree exactly `i` for each `i < d`, then `q₀, …, q_{d-1}` is a basis of
the module of polynomials of degree less than `d`. -/
@[zeta5irr "lem_in_monic_triangular"]
theorem exists_basis_degreeLT_of_monic {R : Type*} [CommRing R] {d : ℕ} (q : Fin d → R[X])
    (hmonic : ∀ i, (q i).Monic) (hdeg : ∀ i, (q i).natDegree = i) :
    ∃ b : Basis (Fin d) R (degreeLT R d), ∀ i, (b i : R[X]) = q i := by
  have hle (i : Fin d) : (q i).degree ≤ (i : ℕ) := (degree_le_natDegree).trans (by simp [hdeg])
  let q' : Fin d → degreeLT R d := fun i ↦
    ⟨q i, mem_degreeLT.2 <| (hle i).trans_lt <| by exact_mod_cast i.is_lt⟩
  refine ⟨degreeLT.basisOfTriangular q' hle fun i ↦ ?_, fun i ↦ by simp [q']⟩
  have := (hmonic i).coeff_natDegree
  rw [hdeg] at this
  simp [q', this]

end Zeta5Irr
