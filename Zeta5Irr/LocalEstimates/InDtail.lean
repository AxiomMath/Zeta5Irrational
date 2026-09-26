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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The tail polynomial `D_tail`

For natural numbers `N ≤ K`, the tail polynomial is
`D_tail(t) = ∏_{j=N+1}^{K} (t + j²)`,
a monic polynomial of degree `K - N` whose roots are `-(N+1)², …, -K²`. It enters the
distributing basis of the inner range.

## Main definitions

* `Zeta5Irr.dTail`: the polynomial `∏_{j=N+1}^{K} (X + j²)` over a commutative ring `R`.

## Main results

* `Zeta5Irr.dTail_monic`: `D_tail` is monic.
* `Zeta5Irr.natDegree_dTail`: `D_tail` has degree `K - N` (over a nontrivial ring).
* `Zeta5Irr.eval_dTail`: `D_tail(t) = ∏_{j=N+1}^{K} (t + j²)`.

## Implementation notes

* The source uses `N = 3n` and `K = 40n`; here `N` and `K` are arbitrary natural numbers, since
  consumers vary both. When `K ≤ N` the product is empty and `D_tail = 1`.
* The source works over `ℚ` and `ℤ_p`; the definition is made over any commutative ring.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4: the inner range, the distributing basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable (R : Type*) [CommRing R]

/-- The tail polynomial `D_tail(t) = ∏_{j=N+1}^{K} (t + j²)` over a commutative ring `R`. -/
@[zeta5irr "def_in_Dtail"]
noncomputable def dTail (N K : ℕ) : R[X] :=
  ∏ j ∈ Icc (N + 1) K, (X + C ((j : R) ^ 2))

variable {R}

/-- The tail polynomial is monic. -/
theorem dTail_monic (N K : ℕ) : (dTail R N K).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- The tail polynomial has degree `K - N`. -/
theorem natDegree_dTail [Nontrivial R] (N K : ℕ) : (dTail R N K).natDegree = K - N := by
  unfold dTail
  rw [natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

/-- Evaluation of the tail polynomial: `D_tail(t) = ∏_{j=N+1}^{K} (t + j²)`. -/
theorem eval_dTail (N K : ℕ) (t : R) :
    (dTail R N K).eval t = ∏ j ∈ Icc (N + 1) K, (t + (j : R) ^ 2) := by
  simp [dTail, eval_prod]

/-- The tail polynomial is `1` when `K ≤ N`. -/
theorem dTail_of_le {N K : ℕ} (h : K ≤ N) : dTail R N K = 1 := by
  rw [dTail, Icc_eq_empty (by omega), prod_empty]

end Zeta5Irr
