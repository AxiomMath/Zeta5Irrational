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
# The limiting pole count at the base `q̃`

The limiting pole count at the base is the step function `q̃(x) = ⌊2 x⌋`. It enters the
limiting functions through `ñ(x) = (2 x - q̃(x)) / 2` and through the combination
`s̃(x) (2 T̃(x) - q̃(x) - 5)`.

## Main definitions

* `Zeta5Irr.basePoleCount`: the limiting pole count at the base `q̃(x) = ⌊2 x⌋`.

## Main results

* `Zeta5Irr.basePoleCount_le`, `Zeta5Irr.sub_one_lt_basePoleCount`: `2 x - 1 < q̃(x) ≤ 2 x`.
* `Zeta5Irr.basePoleCount_nonneg`: `0 ≤ q̃(x)` for `0 ≤ x`.

## Implementation notes

* The source defines `q̃` only for `x ≥ 3`. The formula makes sense for every real `x`, so
  `q̃` is defined on all of `ℝ`, and the restriction `x ≥ 3` is carried by the lemmas that
  use it.
* `q̃` takes integer values but is real-valued, the coercion of `Int.floor`, because it is
  always combined with real quantities.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the pole count at the base.
-/

@[expose] public section

namespace Zeta5Irr

/-- The limiting pole count at the base `q̃(x) = ⌊2 x⌋`.
The source restricts to `x ≥ 3`; the formula is used for all real `x`. -/
@[zeta5irr "def_qx"]
noncomputable def basePoleCount (x : ℝ) : ℝ := ⌊2 * x⌋

/-- Unfolding lemma for `q̃`. -/
theorem basePoleCount_def (x : ℝ) : basePoleCount x = ⌊2 * x⌋ := rfl

/-- `q̃(x) ≤ 2 x`. -/
theorem basePoleCount_le (x : ℝ) : basePoleCount x ≤ 2 * x :=
  Int.floor_le _

/-- `2 x - 1 < q̃(x)`. -/
theorem sub_one_lt_basePoleCount (x : ℝ) : 2 * x - 1 < basePoleCount x :=
  Int.sub_one_lt_floor _

/-- `q̃(x) ≥ 0` for `x ≥ 0`. -/
theorem basePoleCount_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ basePoleCount x :=
  Int.cast_nonneg (Int.floor_nonneg.2 (by linarith))

end Zeta5Irr
