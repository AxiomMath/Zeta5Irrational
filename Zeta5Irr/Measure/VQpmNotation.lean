/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
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
# The bracket `q₋ < q₊` of the minimum of the external field

The external field `V` has a unique minimum on `[0, ∞)`, and it lies between the two rational
numbers `q₋ = 59205077 / 10¹⁰` and `q₊ = 59205079 / 10¹⁰`. This file names these two
constants and records the elementary facts about them that the shape analysis of `V` uses.

## Main definitions

* `Zeta5Irr.externalFieldMinLower`: the lower end `q₋ = 59205077 / 10¹⁰` of the bracket.
* `Zeta5Irr.externalFieldMinUpper`: the upper end `q₊ = 59205079 / 10¹⁰` of the bracket.

## Main results

* `Zeta5Irr.externalFieldMinLower_pos`: `0 < q₋`.
* `Zeta5Irr.externalFieldMinLower_lt_upper`: `q₋ < q₊`.
* `Zeta5Irr.externalFieldMinUpper_pos`: `0 < q₊`.
* `Zeta5Irr.externalFieldMinUpper_lt`: `q₊ < 1 / 100`.
* `Zeta5Irr.externalFieldMinLower_lt`: `q₋ < 1 / 100`.

## Implementation notes

* The source calls the constants `q₋` and `q₊`; they are named here for what they bracket.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5: the shape of the field.
-/

@[expose] public section

namespace Zeta5Irr

/-- The lower end `q₋ = 59205077 / 10¹⁰` of the bracket around the minimum of the external
field. -/
@[zeta5irr "not_V_qpm"]
def externalFieldMinLower : ℚ := 59205077 / 10 ^ 10

/-- The upper end `q₊ = 59205079 / 10¹⁰` of the bracket around the minimum of the external
field. -/
@[zeta5irr "not_V_qpm"]
def externalFieldMinUpper : ℚ := 59205079 / 10 ^ 10

/-- The lower end of the bracket is positive. -/
theorem externalFieldMinLower_pos : 0 < externalFieldMinLower := by
  norm_num [externalFieldMinLower]

/-- The lower end of the bracket is below the upper end. -/
theorem externalFieldMinLower_lt_upper : externalFieldMinLower < externalFieldMinUpper := by
  norm_num [externalFieldMinLower, externalFieldMinUpper]

/-- The upper end of the bracket is positive. -/
theorem externalFieldMinUpper_pos : 0 < externalFieldMinUpper :=
  externalFieldMinLower_pos.trans externalFieldMinLower_lt_upper

/-- The upper end of the bracket is below `1 / 100`. -/
theorem externalFieldMinUpper_lt : externalFieldMinUpper < 1 / 100 := by
  norm_num [externalFieldMinUpper]

/-- The lower end of the bracket is below `1 / 100`. -/
theorem externalFieldMinLower_lt : externalFieldMinLower < 1 / 100 :=
  externalFieldMinLower_lt_upper.trans externalFieldMinUpper_lt

end Zeta5Irr
