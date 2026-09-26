/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import PrimeNumberTheoremAnd.Consequences
public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
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
# The prime number theorem for `ϑ`

The first Chebyshev function `ϑ(y) = ∑_{p ≤ y} log p` satisfies `ϑ(y) / y → 1` as `y → ∞`.
This is the prime number theorem in Chebyshev's form.

## Main results

* `Zeta5Irr.tendsto_theta_div_atTop`: `ϑ(y) / y → 1` as `y → ∞`.

## Implementation notes

* `ϑ` is Mathlib's `Chebyshev.theta`. The prime number theorem is taken from
  PrimeNumberTheoremAnd, where it is stated as the asymptotic equivalence `ϑ ~ id` at `atTop`
  (`chebyshev_asymptotic`); since the identity is eventually nonzero, this equivalence is the
  statement that the quotient tends to `1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.7 (The prime number theorem).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Asymptotics Topology

/-- **The prime number theorem** in Chebyshev's form: `ϑ(y) / y → 1` as `y → ∞`. -/
@[zeta5irr "lem_norm_theta_pnt"]
theorem tendsto_theta_div_atTop :
    Tendsto (fun y : ℝ ↦ Chebyshev.theta y / y) atTop (𝓝 1) :=
  (isEquivalent_iff_tendsto_one (eventually_ne_atTop 0)).1 chebyshev_asymptotic

end Zeta5Irr
