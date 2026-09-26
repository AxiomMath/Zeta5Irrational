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
# The distance function `d₀`

For `0 ≤ u < 1` the function `d₀(u) = min(u, 1 - u)` is the distance from `u` to the nearest
integer. Applied to a fractional part it recovers the distance of any real number to the
nearest integer: `d₀ (fract x) = |x - round x|`.

## Main definitions

* `Zeta5Irr.d₀`: the function `u ↦ min u (1 - u)`.

## Main results

* `Zeta5Irr.d₀_fract`: `d₀ (fract x) = |x - round x|`.
* `Zeta5Irr.d₀_one_sub`: `d₀ (1 - u) = d₀ u`.
* `Zeta5Irr.d₀_le_half`: `d₀ u ≤ 1 / 2`.
* `Zeta5Irr.d₀_nonneg`: `0 ≤ d₀ u` for `0 ≤ u ≤ 1`.

## Implementation notes

The source defines `d₀` only on `[0, 1)`. We define it on all of `ℝ` by the same formula; its
consumers apply it to fractional parts `Int.fract x` and carry the range hypothesis
`0 ≤ u < 1` separately, which avoids coercions from a subtype inside integrals.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1 (fractional parts and the two `z`-integrals).
-/

@[expose] public section

namespace Zeta5Irr

/-- The function `d₀(u) = min(u, 1 - u)`; for `0 ≤ u < 1` it is the distance from `u` to the
nearest integer. -/
@[zeta5irr "def_d0"]
def d₀ (u : ℝ) : ℝ := min u (1 - u)

/-- Unfolding lemma for `d₀`. -/
theorem d₀_def (u : ℝ) : d₀ u = min u (1 - u) := rfl

/-- `d₀` is symmetric about `1 / 2`. -/
theorem d₀_one_sub (u : ℝ) : d₀ (1 - u) = d₀ u := by
  simp [d₀, min_comm]

/-- `d₀` of the fractional part of `x` is the distance from `x` to the nearest integer. -/
theorem d₀_fract (x : ℝ) : d₀ (Int.fract x) = |x - round x| :=
  (abs_sub_round_eq_min x).symm

/-- `d₀ u ≤ 1 / 2` for every `u`. -/
theorem d₀_le_half (u : ℝ) : d₀ u ≤ 1 / 2 := by
  unfold d₀
  rcases le_total u (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- `d₀ u` is nonnegative for `0 ≤ u ≤ 1`. -/
theorem d₀_nonneg {u : ℝ} (h₀ : 0 ≤ u) (h₁ : u ≤ 1) : 0 ≤ d₀ u :=
  le_min h₀ (by linarith)

/-- `d₀` of a fractional part is nonnegative. -/
theorem d₀_fract_nonneg (x : ℝ) : 0 ≤ d₀ (Int.fract x) :=
  d₀_nonneg (Int.fract_nonneg x) (Int.fract_lt_one x).le

end Zeta5Irr
