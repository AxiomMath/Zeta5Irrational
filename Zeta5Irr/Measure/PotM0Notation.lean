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
# The potential bound `M₀`

The comparison measure `ρ` of the equilibrium problem satisfies the potential inequality
`2 U^ρ(t) - V(t) ≤ M₀` for every `t ≥ 0`, where `V` is the external field and
`M₀ = -1329/200` is an explicit rational constant. This file names that constant.

## Main definitions

* `Zeta5Irr.potentialBound`: the constant `M₀ = -1329/200`.

## Main results

* `Zeta5Irr.potentialBound_neg`: `M₀ < 0`.

## Implementation notes

* The source's name for the constant is `M₀`; it is named here for what it is, the upper
  bound of `2 U^ρ - V`. It is a rational number, so that comparisons with it reduce to
  arithmetic in `ℚ`; consumers working over `ℝ` cast it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

/-- The potential bound `M₀ = -1329/200`: the upper bound of `2 U^ρ - V` on `[0, ∞)`, where
`ρ` is the comparison measure and `V` the external field. -/
@[zeta5irr "not_pot_M0"]
def potentialBound : ℚ := -1329 / 200

/-- The potential bound is negative. -/
theorem potentialBound_neg : potentialBound < 0 := by
  unfold potentialBound
  norm_num

end Zeta5Irr
