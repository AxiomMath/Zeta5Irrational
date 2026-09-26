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
# The pole polynomial of a finite set of integers

For a finite set `S ⊆ ℤ`, the polynomial `E_S(x) = ∏_{r ∈ S} (x - r)` is the monic
polynomial whose roots are exactly the elements of `S`, each simple. In particular
`E_∅ = 1` and `deg E_S = #S`. It is the denominator against which the functional `τ_X`
performs Euclidean division.

## Main definitions

* `Zeta5Irr.intPoleProduct`: the polynomial `E_S = ∏_{r ∈ S} (X - r)`.

## Main results

* `Zeta5Irr.intPoleProduct_empty`: `E_∅ = 1`.
* `Zeta5Irr.monic_intPoleProduct`, `Zeta5Irr.natDegree_intPoleProduct`,
  `Zeta5Irr.degree_intPoleProduct`: `E_S` is monic of degree `#S`.
* `Zeta5Irr.eval_intPoleProduct_ne_zero_iff`: over a domain, `E_S(x) ≠ 0` iff `x ∉ S`.
* `Zeta5Irr.eval_intPoleProduct`, `Zeta5Irr.map_intPoleProduct`,
  `Zeta5Irr.derivative_intPoleProduct`: the value, the base change, and the
  derivative `E_S' = ∑_{r ∈ S} E_{S \ {r}}` of `E_S`.

## Implementation notes

The source works in `ℚ[x]`. Here the coefficients lie in an arbitrary commutative
ring, with the integers `r ∈ S` cast into it; the source's polynomial is the case
`R = ℚ`, and any other coefficient ring is related to it by
`Zeta5Irr.map_intPoleProduct`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3: the functional `τ_X`.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- The pole polynomial `E_S(x) = ∏_{r ∈ S} (x - r)` of a finite set `S ⊆ ℤ`: the monic
polynomial whose roots are the elements of `S`. -/
@[zeta5irr "def_tau_poles"]
noncomputable def intPoleProduct (S : Finset ℤ) (R : Type*) [CommRing R] : R[X] :=
  ∏ r ∈ S, (X - C (r : R))

variable (S : Finset ℤ) (R : Type*) [CommRing R]

/-- The pole polynomial of the empty set is `E_∅ = 1`. -/
@[zeta5irr "def_tau_poles", simp]
theorem intPoleProduct_empty : intPoleProduct ∅ R = 1 := by
  rw [intPoleProduct, prod_empty]

/-- Adding a new integer `r` to `S` multiplies `E_S` by `x - r`. -/
theorem intPoleProduct_insert {r : ℤ} {S : Finset ℤ} (h : r ∉ S) :
    intPoleProduct (insert r S) R = (X - C (r : R)) * intPoleProduct S R := by
  rw [intPoleProduct, intPoleProduct, prod_insert h]

/-- The pole polynomial of a singleton is `E_{r} = x - r`. -/
@[simp]
theorem intPoleProduct_singleton (r : ℤ) : intPoleProduct {r} R = X - C (r : R) := by
  rw [intPoleProduct, prod_singleton]

/-- The pole polynomial `E_S` is monic. -/
theorem monic_intPoleProduct : (intPoleProduct S R).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

/-- The pole polynomial `E_S` is nonzero over a nontrivial ring. -/
theorem intPoleProduct_ne_zero [Nontrivial R] : intPoleProduct S R ≠ 0 :=
  (monic_intPoleProduct S R).ne_zero

/-- The natural degree of `E_S` is `#S`. -/
@[zeta5irr "def_tau_poles", simp]
theorem natDegree_intPoleProduct [Nontrivial R] : (intPoleProduct S R).natDegree = #S := by
  rw [intPoleProduct, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

/-- The degree of `E_S` is `#S`. -/
@[zeta5irr "def_tau_poles"]
theorem degree_intPoleProduct [Nontrivial R] : (intPoleProduct S R).degree = #S := by
  rw [degree_eq_natDegree (intPoleProduct_ne_zero S R), natDegree_intPoleProduct]

/-- The value of `E_S` at `x` is `∏_{r ∈ S} (x - r)`. -/
@[simp]
theorem eval_intPoleProduct (x : R) :
    (intPoleProduct S R).eval x = ∏ r ∈ S, (x - (r : R)) := by
  simp only [intPoleProduct, eval_prod, eval_sub, eval_X, eval_C]

/-- Every element of `S` is a root of `E_S`. -/
theorem eval_intPoleProduct_of_mem {r : ℤ} (hr : r ∈ S) :
    (intPoleProduct S R).eval (r : R) = 0 := by
  rw [eval_intPoleProduct]
  exact prod_eq_zero hr (sub_self _)

/-- Over a domain, `E_S` does not vanish at `x` if and only if `x` is none of the elements
of `S`. -/
theorem eval_intPoleProduct_ne_zero_iff [IsDomain R] {x : R} :
    (intPoleProduct S R).eval x ≠ 0 ↔ ∀ r ∈ S, x ≠ r := by
  simp [prod_ne_zero_iff, sub_ne_zero]

/-- If `U = P E_S + B` with `deg B < #S`, then `P` is the quotient `U /ₘ E_S`. -/
theorem divByMonic_intPoleProduct_eq_of_eq_mul_add [Nontrivial R] {U P B : R[X]}
    (hU : U = P * intPoleProduct S R + B) (hB : B.degree < #S) :
    U /ₘ intPoleProduct S R = P := by
  refine (div_modByMonic_unique P B (monic_intPoleProduct S R) ⟨?_, ?_⟩).1
  · rw [hU]; ring
  · rwa [degree_intPoleProduct]

/-- The pole polynomial commutes with base change along a ring homomorphism. -/
theorem map_intPoleProduct {R' : Type*} [CommRing R'] (f : R →+* R') :
    (intPoleProduct S R).map f = intPoleProduct S R' := by
  simp [intPoleProduct, Polynomial.map_prod]

/-- The derivative of the pole polynomial: `E_S' = ∑_{r ∈ S} E_{S \ {r}}`, since every
factor of `E_S` is monic of degree one. -/
theorem derivative_intPoleProduct :
    derivative (intPoleProduct S R) = ∑ r ∈ S, intPoleProduct (S.erase r) R := by
  rw [intPoleProduct, derivative_prod_finset]
  exact sum_congr rfl fun r _ ↦ by rw [derivative_X_sub_C, mul_one, intPoleProduct]

end Zeta5Irr
