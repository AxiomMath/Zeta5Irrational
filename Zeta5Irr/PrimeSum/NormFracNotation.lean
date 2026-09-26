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
# The fractional part `{x} = x - ⌊x⌋`

For a real number `x`, the source writes `{x}` for the fractional part `x - ⌊x⌋`. This is
Mathlib's `Int.fract`, which is defined for every linearly ordered ring with a floor; this file
records that it is the source's `{x}`.

## Main results

* `Zeta5Irr.fract_eq_sub_floor`: `Int.fract x = x - ⌊x⌋`.

## Implementation notes

* The source's `{x}` is not given a new definition: it is Mathlib's `Int.fract x`, and the
  statement is proved for an arbitrary linearly ordered ring with a floor rather than for `ℝ`
  only.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8 (Normalization and the prime sum).
-/

@[expose] public section

namespace Zeta5Irr

/-- The fractional part `{x}` of the source is Mathlib's `Int.fract x`, namely `x - ⌊x⌋`. -/
@[zeta5irr "not_norm_frac"]
theorem fract_eq_sub_floor {α : Type*} [Ring α] [LinearOrder α] [FloorRing α] (x : α) :
    Int.fract x = x - ⌊x⌋ :=
  rfl

end Zeta5Irr
