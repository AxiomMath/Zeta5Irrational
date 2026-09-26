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
# The final rational margin `A_*`

The explicit rational constant
`A_* = 9928298118277006344769 / 7535670527041937280000 ≈ 1.3175`
entering the final rational margin of the irrationality argument.

## Main definitions

* `Zeta5Irr.Astar`: the rational number `A_*`.

## Main results

* `Zeta5Irr.Astar_pos`: `0 < A_*`.
* `Zeta5Irr.one_lt_Astar`: `1 < A_*`.

## Implementation notes

`A_*` is defined as an exact element of `ℚ` rather than of `ℝ`, so that numerical claims about
it can be discharged by `norm_num` or `decide`; it is coerced to `ℝ` where it is used.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.5 (the final rational margin).
-/

@[expose] public section

namespace Zeta5Irr

/-- The final rational margin
`A_* = 9928298118277006344769 / 7535670527041937280000`. -/
@[zeta5irr "def_Astar"]
def Astar : ℚ := 9928298118277006344769 / 7535670527041937280000

/-- `A_*` is positive. -/
theorem Astar_pos : 0 < Astar := by
  unfold Astar; norm_num

/-- `A_*` exceeds `1`. -/
theorem one_lt_Astar : 1 < Astar := by
  unfold Astar; norm_num

end Zeta5Irr
