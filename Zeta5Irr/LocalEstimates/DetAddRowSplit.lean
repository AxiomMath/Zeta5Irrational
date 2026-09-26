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
# Row-splitting expansion of the determinant of a sum

Let `A` and `B` be square matrices over a commutative ring `R`, indexed by a finite type `n`.
For a set `I` of rows, let `M_I` be the matrix whose `r`th row is the `r`th row of `B` when
`r ∈ I` and the `r`th row of `A` otherwise. Since the determinant is multilinear in the rows,
`det (A + B) = ∑_I det M_I`, the sum running over all subsets `I` of the row index set.

## Main results

* `Zeta5Irr.det_add_eq_sum_det_rowSplit`: `det (A + B) = ∑ I, det (of fun r ↦ if r ∈ I then B r
  else A r)`.

## Implementation notes

The source states this for `h × h` matrices with `h ≥ 1`, proving it by splitting one row at a
time with `Matrix.det_updateRow_add`. We state it for an arbitrary finite index type `n`, where
the hypothesis `h ≥ 1` is not needed (for `n` empty both sides equal `1`), and deduce it in one
step from the expansion `MultilinearMap.map_add_univ` of a multilinear map at a sum, applied to
the determinant as the alternating map `Matrix.detRowAlternating` of the rows.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4 (valuation and determinant preliminaries).
-/

@[expose] public section

namespace Zeta5Irr

open Matrix

/-- The determinant of `A + B` is the sum, over all sets `I` of rows, of the determinant of the
matrix taking its rows in `I` from `B` and its other rows from `A`. -/
@[zeta5irr "lem_out_det_rowsplit"]
theorem det_add_eq_sum_det_rowSplit {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A B : Matrix n n R) :
    (A + B).det = ∑ I : Finset n, (Matrix.of fun r ↦ if r ∈ I then B r else A r).det := by
  rw [add_comm]
  exact (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_add_univ B A

end Zeta5Irr
