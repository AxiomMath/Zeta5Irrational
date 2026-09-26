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
# The multiple-of-`p` pole products `q_{0,i}`

For a prime `p` and `0 ≤ i < m_K - m_N`, the source sets
`q_{0,i}(t) = ∏_{k=1}^{i} (t + (k p)²)`,
the product of the linear factors `t + j²` over the first `i` multiples `j = p, 2p, …, ip` of
`p`. It is a monic polynomial of degree `i` with integer coefficients; these products make up
the residue class `0` of the separating basis of the outer range.

## Main definitions

* `Zeta5Irr.multiplePoleProduct`: the polynomial `∏_{k=1}^{i} (X + (k p)²)` over a commutative
  ring `R`.

## Main results

* `Zeta5Irr.multiplePoleProduct_monic`: `q_{0,i}` is monic.
* `Zeta5Irr.natDegree_multiplePoleProduct`: `q_{0,i}` has degree `i` (over a nontrivial ring).
* `Zeta5Irr.eval_multiplePoleProduct`: `q_{0,i}(t) = ∏_{k=1}^{i} (t + (k p)²)`.
* `Zeta5Irr.map_multiplePoleProduct`: `q_{0,i}` is the image of the integer polynomial
  `q_{0,i}` under any ring homomorphism.
* `Zeta5Irr.multiplePoleProduct_succ`: `q_{0,i+1} = q_{0,i} · (X + ((i+1) p)²)`.

## Implementation notes

* The range `0 ≤ i < m_K - m_N` is a constraint on the consumers of `q_{0,i}`, not on its
  definition, so `i` is an arbitrary natural number here; `q_{0,0} = 1`.
* Primality of `p` is not needed to define `q_{0,i}`, so `p` is an arbitrary natural number.
* The source works with integer coefficients; the definition is made over any commutative ring
  `R`, and `map_multiplePoleProduct` identifies each instance with the image of the one over
  `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The multiple-of-`p` pole product `q_{0,i} = ∏_{k=1}^{i} (X + (k p)²)`. -/
@[zeta5irr "def_out_q0"]
noncomputable def multiplePoleProduct (R : Type*) [CommRing R] (p i : ℕ) : R[X] :=
  ∏ k ∈ Icc 1 i, (X + C (((k * p : ℕ) : R) ^ 2))

/-- The empty product: `q_{0,0} = 1`. -/
@[simp]
theorem multiplePoleProduct_zero (p : ℕ) : multiplePoleProduct R p 0 = 1 := by
  simp [multiplePoleProduct]

/-- The recursion `q_{0,i+1} = q_{0,i} · (X + ((i+1) p)²)`. -/
theorem multiplePoleProduct_succ (p i : ℕ) :
    multiplePoleProduct R p (i + 1) =
      multiplePoleProduct R p i * (X + C ((((i + 1) * p : ℕ) : R) ^ 2)) := by
  simp only [multiplePoleProduct]
  exact prod_Icc_succ_top (by omega) _

/-- `q_{0,i}` is monic. -/
theorem multiplePoleProduct_monic (p i : ℕ) : (multiplePoleProduct R p i).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- `q_{0,i}` has degree `i`. -/
theorem natDegree_multiplePoleProduct [Nontrivial R] (p i : ℕ) :
    (multiplePoleProduct R p i).natDegree = i := by
  rw [multiplePoleProduct, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

/-- Evaluation: `q_{0,i}(t) = ∏_{k=1}^{i} (t + (k p)²)`. -/
@[simp]
theorem eval_multiplePoleProduct (p i : ℕ) (t : R) :
    (multiplePoleProduct R p i).eval t = ∏ k ∈ Icc 1 i, (t + ((k * p : ℕ) : R) ^ 2) := by
  simp [multiplePoleProduct, eval_prod]

/-- `q_{0,i}` over `S` is the image of `q_{0,i}` over `R` under any ring homomorphism. -/
@[simp]
theorem map_multiplePoleProduct (f : R →+* S) (p i : ℕ) :
    (multiplePoleProduct R p i).map f = multiplePoleProduct S p i := by
  simp [multiplePoleProduct, Polynomial.map_prod]

end Zeta5Irr
