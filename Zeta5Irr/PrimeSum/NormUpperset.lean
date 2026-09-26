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
public import Mathlib.RingTheory.WittVector.IsPoly
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
# The step set `S(x)` of the pole counts

For `x : ℝ` with fractional part `{x} = x - ⌊x⌋`, the set
`S(x) = (0, {x}]` if `{x} < 1/2`, and `S(x) = [1 - {x}, 1/2)` if `{x} ≥ 1/2`,
is an interval contained in `(0, 1/2)` which depends on `x` only through `{x}`.
Its Lebesgue measure is `{x}` in the first case and `{x} - 1/2` in the second.

## Main definitions

* `Zeta5Irr.normUpperSet`: the set `S(x)`.

## Main results

* `Zeta5Irr.mem_normUpperSet`: membership in `S(x)`, case by case.
* `Zeta5Irr.normUpperSet_subset_Ioo`: `S(x) ⊆ (0, 1/2)`.
* `Zeta5Irr.measurableSet_normUpperSet`: `S(x)` is measurable.
* `Zeta5Irr.volume_normUpperSet`: the Lebesgue measure of `S(x)`.
* `Zeta5Irr.normUpperSet_add_intCast`: `S(x + n) = S(x)` for `n : ℤ`.

## Implementation notes

* `S(x)` is a `Set ℝ` rather than a subtype, so that indicators, intersections and
  measures of it can be taken directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2: the step structure of the pole counts.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- The step set `S(x)`: `(0, {x}]` when `{x} < 1/2`, and `[1 - {x}, 1/2)` otherwise. -/
@[zeta5irr "def_norm_upperset"]
noncomputable def normUpperSet (x : ℝ) : Set ℝ :=
  if Int.fract x < 1 / 2 then Set.Ioc 0 (Int.fract x) else Set.Ico (1 - Int.fract x) (1 / 2)

/-- `S(x) = (0, {x}]` when `{x} < 1/2`. -/
theorem normUpperSet_of_lt {x : ℝ} (hx : Int.fract x < 1 / 2) :
    normUpperSet x = Set.Ioc 0 (Int.fract x) := by
  simp only [normUpperSet, hx, ite_true]

/-- `S(x) = [1 - {x}, 1/2)` when `{x} ≥ 1/2`. -/
theorem normUpperSet_of_le {x : ℝ} (hx : 1 / 2 ≤ Int.fract x) :
    normUpperSet x = Set.Ico (1 - Int.fract x) (1 / 2) := by
  simp only [normUpperSet, hx.not_gt, ite_false]

/-- Membership in `S(x)`, case by case. -/
theorem mem_normUpperSet {x t : ℝ} :
    t ∈ normUpperSet x ↔ (Int.fract x < 1 / 2 ∧ 0 < t ∧ t ≤ Int.fract x) ∨
      (1 / 2 ≤ Int.fract x ∧ 1 - Int.fract x ≤ t ∧ t < 1 / 2) := by
  rcases lt_or_ge (Int.fract x) (1 / 2) with h | h
  · rw [normUpperSet_of_lt h, Set.mem_Ioc]
    exact ⟨fun ht ↦ .inl ⟨h, ht⟩, fun ht ↦ ht.elim (·.2) fun ht ↦ absurd ht.1 h.not_ge⟩
  · rw [normUpperSet_of_le h, Set.mem_Ico]
    exact ⟨fun ht ↦ .inr ⟨h, ht⟩, fun ht ↦ ht.elim (fun ht ↦ absurd ht.1 h.not_gt) (·.2)⟩

/-- `S(x)` is contained in `(0, 1/2)`. -/
theorem normUpperSet_subset_Ioo (x : ℝ) : normUpperSet x ⊆ Set.Ioo 0 (1 / 2) := by
  intro t ht
  have h1 := Int.fract_lt_one x
  rcases mem_normUpperSet.1 ht with ⟨h, h0, ht⟩ | ⟨h, h0, ht⟩
  · exact ⟨h0, ht.trans_lt h⟩
  · exact ⟨by linarith, ht⟩

/-- `S(x)` is a measurable set. -/
theorem measurableSet_normUpperSet (x : ℝ) : MeasurableSet (normUpperSet x) := by
  unfold normUpperSet
  split_ifs
  exacts [measurableSet_Ioc, measurableSet_Ico]

/-- The Lebesgue measure of `S(x)`: `{x}` if `{x} < 1/2`, and `{x} - 1/2` otherwise. -/
theorem volume_normUpperSet (x : ℝ) :
    volume (normUpperSet x) =
      ENNReal.ofReal (if Int.fract x < 1 / 2 then Int.fract x else Int.fract x - 1 / 2) := by
  rcases lt_or_ge (Int.fract x) (1 / 2) with h | h
  · rw [normUpperSet_of_lt h, Real.volume_Ioc, sub_zero]
    simp only [h, ite_true]
  · rw [normUpperSet_of_le h, Real.volume_Ico]
    simp only [h.not_gt, ite_false]
    congr 1
    ring

/-- `S(x)` depends only on the fractional part of `x`. -/
theorem normUpperSet_fract (x : ℝ) : normUpperSet (Int.fract x) = normUpperSet x := by
  simp [normUpperSet]

/-- `S(x + n) = S(x)` for every integer `n`. -/
theorem normUpperSet_add_intCast (x : ℝ) (n : ℤ) :
    normUpperSet (x + n) = normUpperSet x := by
  simp [normUpperSet]

end Zeta5Irr
