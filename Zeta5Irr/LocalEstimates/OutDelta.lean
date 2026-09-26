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
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The offset `δ_a` of the outer range

For an integer `a`, the offset `δ_a` is `1` if `a ≤ N` and `0` if `a > N`. It is subtracted
from degree and index bounds in the construction of the separating basis of the outer range.

## Main definitions

* `Zeta5Irr.outerDelta`: the offset `δ_a`, as a natural number.

## Main results

* `Zeta5Irr.outerDelta_of_le`: `δ_a = 1` when `a ≤ N`.
* `Zeta5Irr.outerDelta_of_lt`: `δ_a = 0` when `N < a`.
* `Zeta5Irr.outerDelta_le_one`: `δ_a ≤ 1`.

## Implementation notes

* In the source `N = 3 n` is fixed; here `N` is an explicit integer argument, so that the
  definition applies to any threshold. Callers pass `(innerDegree n : ℤ)`.
* The value is a natural number, since it is used as a truncated offset `K(a) - δ_a`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

/-- The offset `δ_a` with threshold `N`: equal to `1` if `a ≤ N` and to `0` if `a > N`. -/
@[zeta5irr "def_out_delta"]
def outerDelta (N a : ℤ) : ℕ := if a ≤ N then 1 else 0

/-- `δ_a = 1` when `a ≤ N`. -/
@[simp]
theorem outerDelta_of_le {N a : ℤ} (h : a ≤ N) : outerDelta N a = 1 := by simp [outerDelta, h]

/-- `δ_a = 0` when `N < a`. -/
@[simp]
theorem outerDelta_of_lt {N a : ℤ} (h : N < a) : outerDelta N a = 0 := by
  simp [outerDelta, h.not_ge]

/-- `δ_a ≤ 1`. -/
theorem outerDelta_le_one (N a : ℤ) : outerDelta N a ≤ 1 := by
  unfold outerDelta; split_ifs <;> simp

/-- `δ_a = 1` if and only if `a ≤ N`. -/
theorem outerDelta_eq_one_iff {N a : ℤ} : outerDelta N a = 1 ↔ a ≤ N := by
  unfold outerDelta; split_ifs with h <;> simp [h]

/-- `δ_a = 0` if and only if `N < a`. -/
theorem outerDelta_eq_zero_iff {N a : ℤ} : outerDelta N a = 0 ↔ N < a := by
  unfold outerDelta; split_ifs with h <;> simp [h, not_le.mp]

end Zeta5Irr
