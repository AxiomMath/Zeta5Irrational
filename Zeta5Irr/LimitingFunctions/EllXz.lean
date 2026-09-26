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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The integer-valued function `ℓ(x, z)`

For real `x` and `z` the function
`ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`
is an integer. In the source it is used for `0 ≤ z ≤ 1/2`, and it enters the limiting
integrands of §6 alongside the inner limiting function `T̃`.

## Main definitions

* `Zeta5Irr.ell`: the function `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`.

## Main results

* `Zeta5Irr.ell_zero_right`: `ℓ(x, 0) = 2 ⌊x⌋ + 1`.
* `Zeta5Irr.ell_add_intCast`: `ℓ(x + m, z) = ℓ(x, z) + 2 m` for an integer `m`.
* `Zeta5Irr.ell_le`, `Zeta5Irr.lt_ell`: `2 x - 1 < ℓ(x, z) ≤ 2 x + 1`.

## Implementation notes

* The source states the definition for `0 ≤ z ≤ 1/2`. The formula makes sense for all real
  `z`, so `ℓ` is defined on `ℝ × ℝ`, and the constraint on `z` is a hypothesis of the lemmas
  that need it. None of the lemmas in this file need it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The integer `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`, for all real `x` and `z`. -/
@[zeta5irr "def_ell_xz"]
noncomputable def ell (x z : ℝ) : ℤ := ⌊x - z⌋ + ⌊x + z⌋ + 1

/-- `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`. -/
theorem ell_def (x z : ℝ) : ell x z = ⌊x - z⌋ + ⌊x + z⌋ + 1 := rfl

/-- `ℓ(x, 0) = 2 ⌊x⌋ + 1`. -/
@[simp]
theorem ell_zero_right (x : ℝ) : ell x 0 = 2 * ⌊x⌋ + 1 := by
  simp [ell_def, two_mul]

/-- `ℓ` is even in `z`: `ℓ(x, -z) = ℓ(x, z)`. -/
theorem ell_neg_right (x z : ℝ) : ell x (-z) = ell x z := by
  simp only [ell_def, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- Shifting `x` by an integer `m` shifts `ℓ` by `2 m`. -/
theorem ell_add_intCast (x z : ℝ) (m : ℤ) : ell (x + m) z = ell x z + 2 * m := by
  have h₁ : x + m - z = x - z + m := by ring
  have h₂ : x + m + z = x + z + m := by ring
  rw [ell_def, ell_def, h₁, h₂, Int.floor_add_intCast, Int.floor_add_intCast]
  ring

/-- `ℓ(x, z) ≤ 2 x + 1`. -/
theorem ell_le (x z : ℝ) : (ell x z : ℝ) ≤ 2 * x + 1 := by
  have h₁ := Int.floor_le (x - z)
  have h₂ := Int.floor_le (x + z)
  push_cast [ell_def]
  linarith

/-- `2 x - 1 < ℓ(x, z)`. -/
theorem lt_ell (x z : ℝ) : 2 * x - 1 < (ell x z : ℝ) := by
  have h₁ := Int.lt_floor_add_one (x - z)
  have h₂ := Int.lt_floor_add_one (x + z)
  push_cast [ell_def]
  linarith

/-- `|ℓ(x, z)| ≤ 2 |x| + 1`. -/
theorem abs_ell_le (x z : ℝ) : |(ell x z : ℝ)| ≤ 2 * |x| + 1 :=
  abs_le.2 ⟨by linarith [lt_ell x z, neg_abs_le x], by linarith [ell_le x z, le_abs_self x]⟩

end Zeta5Irr
