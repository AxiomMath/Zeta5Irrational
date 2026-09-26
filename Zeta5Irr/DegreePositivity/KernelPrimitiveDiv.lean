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
public import Mathlib.Tactic.ENatToNat
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
# Division of the kernel's primitive

Polynomial division of `y ^ 5` by `y ^ 2 + b ^ 2` gives quotient `y ^ 3 - b ^ 2 * y` and
remainder `b ^ 4 * y`, so that
`y ^ 5 / (y ^ 2 + b ^ 2) = y ^ 3 - b ^ 2 * y + b ^ 4 * y / (y ^ 2 + b ^ 2)`.

## Main results

* `Zeta5Irr.pow_five_div_sq_add_sq`: the division identity, in any field, whenever
  `y ^ 2 + b ^ 2 ≠ 0`.
* `Zeta5Irr.pow_five_div_sq_add_sq_of_pos`: the real form, for `0 < b`.

## Implementation notes

The source states the identity for real `b > 0`; the only property used is that
`y ^ 2 + b ^ 2` is nonzero, so the main statement is made over an arbitrary field under that
hypothesis, and the source's form is recovered as a corollary.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- Division of `y ^ 5` by `y ^ 2 + b ^ 2`, in any field, whenever the divisor is nonzero. -/
theorem pow_five_div_sq_add_sq {K : Type*} [Field K] {b y : K} (h : y ^ 2 + b ^ 2 ≠ 0) :
    y ^ 5 / (y ^ 2 + b ^ 2) = y ^ 3 - b ^ 2 * y + b ^ 4 * y / (y ^ 2 + b ^ 2) := by
  field_simp
  ring

/-- **Division of the kernel's primitive.** For real `b > 0` and every real `y`,
`y ^ 5 / (y ^ 2 + b ^ 2) = y ^ 3 - b ^ 2 * y + b ^ 4 * y / (y ^ 2 + b ^ 2)`. -/
@[zeta5irr "lem_w_ker_div"]
theorem pow_five_div_sq_add_sq_of_pos {b : ℝ} (hb : 0 < b) (y : ℝ) :
    y ^ 5 / (y ^ 2 + b ^ 2) = y ^ 3 - b ^ 2 * y + b ^ 4 * y / (y ^ 2 + b ^ 2) :=
  pow_five_div_sq_add_sq (by positivity)

end Zeta5Irr
