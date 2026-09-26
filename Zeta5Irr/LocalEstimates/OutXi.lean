/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutQ
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
# The residue-class polynomial `Ξ_a`

For a prime `p`, an integer `a` and the pole bound `K`, the source sets
`Ξ_a(t) = ∏_{p < j ≤ K, j ≡ ±a (mod p)} (t + j²)`,
the product of the linear factors `t + j²` over the poles `j` beyond `p` lying in the pair of
residue classes `±a` modulo `p`. It is a monic polynomial whose degree is the number of such
`j`, and it is a building block of the separating basis of the outer range.

## Main definitions

* `Zeta5Irr.outXi`: the polynomial `∏_{p < j ≤ K, j ≡ ±a (mod p)} (X + j²)` over a commutative
  ring `R`.

## Main results

* `Zeta5Irr.outXi_eq_residuePoleProduct`: `Ξ_a` is `Q_a` with lower end `p` (by definition);
  the basic API below is transferred from `Q_a`.
* `Zeta5Irr.outXi_monic`: `Ξ_a` is monic.
* `Zeta5Irr.natDegree_outXi`: the degree of `Ξ_a` is the number of `p < j ≤ K` with
  `j ≡ ±a (mod p)` (over a nontrivial ring).
* `Zeta5Irr.eval_outXi`: `Ξ_a(t) = ∏_{p < j ≤ K, j ≡ ±a (mod p)} (t + j²)`.
* `Zeta5Irr.outXi_neg`: `Ξ_{-a} = Ξ_a`.
* `Zeta5Irr.map_outXi`: `Ξ_a` commutes with ring homomorphisms.

## Implementation notes

* The source uses `K = 40 n`; here `K` is an arbitrary natural number, as for the other
  products over the poles.
* The congruence `j ≡ ±a (mod p)` is stated in `ZMod p`, as `(j : ZMod p) = a ∨ (j : ZMod p) = -a`.
* The source takes `p` prime; primality is not needed for the definition, so `p` is an
  arbitrary natural number.
* The source works over `ℚ` and `ℤ_p`; the definition is made over any commutative ring.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable (R : Type*) [CommRing R]

/-- The residue-class polynomial `Ξ_a(t) = ∏_{p < j ≤ K, j ≡ ±a (mod p)} (t + j²)` over a
commutative ring `R`. -/
@[zeta5irr "def_out_Xi"]
noncomputable def outXi (p K : ℕ) (a : ℤ) : R[X] :=
  ∏ j ∈ (Ioc p K).filter (fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a),
    (X + C ((j : R) ^ 2))

variable {R}

/-- `Ξ_a` is the residue-class pole product `Q_a` with lower end `p`:
`Ξ_a = ∏_{p < j ≤ K, j ≡ ±a (mod p)} (t + j²)`. -/
theorem outXi_eq_residuePoleProduct (p K : ℕ) (a : ℤ) :
    outXi R p K a = residuePoleProduct R p a p K :=
  rfl

/-- The residue-class polynomial is monic. -/
theorem outXi_monic (p K : ℕ) (a : ℤ) : (outXi R p K a).Monic :=
  residuePoleProduct_monic p a p K

/-- The degree of the residue-class polynomial is the number of `p < j ≤ K` with
`j ≡ ±a (mod p)`. -/
theorem natDegree_outXi [Nontrivial R] (p K : ℕ) (a : ℤ) :
    (outXi R p K a).natDegree =
      #((Ioc p K).filter (fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a)) :=
  natDegree_residuePoleProduct p a p K

/-- Evaluation of the residue-class polynomial:
`Ξ_a(t) = ∏_{p < j ≤ K, j ≡ ±a (mod p)} (t + j²)`. -/
theorem eval_outXi (p K : ℕ) (a : ℤ) (t : R) :
    (outXi R p K a).eval t =
      ∏ j ∈ (Ioc p K).filter (fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a),
        (t + (j : R) ^ 2) :=
  eval_residuePoleProduct p a p K t

/-- The residue-class polynomial depends only on the pair `±a`: `Ξ_{-a} = Ξ_a`. -/
theorem outXi_neg (p K : ℕ) (a : ℤ) : outXi R p K (-a) = outXi R p K a :=
  residuePoleProduct_neg p a p K

/-- The residue-class polynomial `Ξ_a` commutes with ring homomorphisms. -/
theorem map_outXi {S : Type*} [CommRing S] (f : R →+* S) (p K : ℕ) (a : ℤ) :
    (outXi R p K a).map f = outXi S p K a :=
  map_residuePoleProduct f p a p K

end Zeta5Irr
