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
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The sign function `e`

For `0 ≤ u < 1` the function `e(u)` is `1` when `u ≤ 1 / 2` and `-1` when `u > 1 / 2`: it
records on which half of the unit interval `u` lies, i.e. whether the nearest integer to `u`
is `0` or `1`.

## Main definitions

* `Zeta5Irr.esign`: the function `u ↦ if u ≤ 1 / 2 then 1 else -1`.

## Main results

* `Zeta5Irr.esign_of_le`, `Zeta5Irr.esign_of_lt`: the two cases of the definition.
* `Zeta5Irr.esign_mul_self`, `Zeta5Irr.esign_sq`: `e(u)² = 1`.
* `Zeta5Irr.abs_esign`: `|e(u)| = 1`.

## Implementation notes

* The source defines `e` only on `[0, 1)`. We define it on all of `ℝ` by the same formula;
  its consumers apply it to fractional parts `Int.fract x` and carry the range hypothesis
  separately.
* The value is real rather than a `SignType`, since `e(u)` is multiplied into real integrals
  and a `SignType` would require a cast at every use.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1 (fractional parts and the two `z`-integrals).
-/

@[expose] public section

namespace Zeta5Irr

/-- The sign `e(u)`, equal to `1` if `u ≤ 1 / 2` and to `-1` otherwise. For `0 ≤ u < 1` it
records whether `u` lies in the lower or upper half of the unit interval. -/
@[zeta5irr "def_esign"]
noncomputable def esign (u : ℝ) : ℝ := if u ≤ 1 / 2 then 1 else -1

/-- Unfolding lemma for `esign`. -/
theorem esign_def (u : ℝ) : esign u = if u ≤ 1 / 2 then 1 else -1 := rfl

/-- `e(u) = 1` for `u ≤ 1 / 2`. -/
@[simp]
theorem esign_of_le {u : ℝ} (h : u ≤ 1 / 2) : esign u = 1 :=
  ite_eq_left_iff.2 fun h' => absurd h h'

/-- `e(u) = -1` for `u > 1 / 2`. -/
@[simp]
theorem esign_of_lt {u : ℝ} (h : 1 / 2 < u) : esign u = -1 :=
  ite_eq_right_iff.2 fun h' => absurd h' (not_le.2 h)

/-- `e(u) = 1` exactly when `u ≤ 1 / 2`. -/
theorem esign_eq_one_iff {u : ℝ} : esign u = 1 ↔ u ≤ 1 / 2 := by
  unfold esign; split_ifs with h <;> norm_num [h]

/-- `e(u) = -1` exactly when `u > 1 / 2`. -/
theorem esign_eq_neg_one_iff {u : ℝ} : esign u = -1 ↔ 1 / 2 < u := by
  unfold esign; split_ifs with h <;> norm_num [h]; linarith

/-- `e(u)` takes only the values `1` and `-1`. -/
theorem esign_eq_one_or_eq_neg_one (u : ℝ) : esign u = 1 ∨ esign u = -1 := by
  unfold esign; split_ifs <;> simp

/-- `e(u) ≠ 0`. -/
theorem esign_ne_zero (u : ℝ) : esign u ≠ 0 := by
  rcases esign_eq_one_or_eq_neg_one u with h | h <;> rw [h] <;> norm_num

/-- `e(u) · e(u) = 1`. -/
@[simp]
theorem esign_mul_self (u : ℝ) : esign u * esign u = 1 := by
  rcases esign_eq_one_or_eq_neg_one u with h | h <;> rw [h] <;> norm_num

/-- `e(u)² = 1`. -/
@[simp]
theorem esign_sq (u : ℝ) : esign u ^ 2 = 1 := by
  rw [sq, esign_mul_self]

/-- `|e(u)| = 1`. -/
@[simp]
theorem abs_esign (u : ℝ) : |esign u| = 1 := by
  rcases esign_eq_one_or_eq_neg_one u with h | h <;> rw [h] <;> norm_num

end Zeta5Irr
