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
public import Mathlib.LinearAlgebra.Lagrange
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
# The derivative of `∏ (x - ρ_η)` at a root

Let `R` be a commutative ring, `s` a finite set of indices and `v : ι → R`. The derivative of the
polynomial `∏_{j ∈ s} (X - v j)`, evaluated at a node `v i` with `i ∈ s`, equals
`∏_{j ∈ s \ {i}} (v i - v j)`. By the product rule the derivative is
`∑_{k ∈ s} ∏_{j ∈ s \ {k}} (X - v j)`; at `X = v i` every summand with `k ≠ i` contains the factor
`v i - v i = 0`, and only the summand `k = i` survives.

## Main results

* `Zeta5Irr.eval_derivative_prod_X_sub_C`:
  `(∏_{j ∈ s} (X - v j))'(v i) = ∏_{j ∈ s \ {i}} (v i - v j)`.

## Implementation notes

The source states this over a field with pairwise distinct `ρ_η`; neither hypothesis is used, so
the lemma is stated over a commutative ring for an arbitrary family `v`. The set `Λ \ {η₀}` is
written `s.erase i`, which is Mathlib's normal form for it (`Finset.sdiff_singleton_eq_erase`).
The statement is `Lagrange.eval_nodal_derivative_eval_node_eq` for the nodal polynomial
`Lagrange.nodal s v = ∏_{j ∈ s} (X - C (v j))`, rewritten without `Lagrange.nodal`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The derivative of `∏_{j ∈ s} (X - v j)` at the node `v i`, `i ∈ s`, is
`∏_{j ∈ s \ {i}} (v i - v j)`. -/
@[zeta5irr "lem_tau_dprod"]
theorem eval_derivative_prod_X_sub_C {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (v : ι → R) {i : ι} (hi : i ∈ s) :
    (derivative (∏ j ∈ s, (X - C (v j)))).eval (v i) = ∏ j ∈ s.erase i, (v i - v j) := by
  rw [← Lagrange.nodal_eq, Lagrange.eval_nodal_derivative_eval_node_eq hi, Lagrange.eval_nodal]

end Zeta5Irr
