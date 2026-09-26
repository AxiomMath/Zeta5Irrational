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
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The inner limiting function `𝒥`

For `u ≥ 0` the inner limiting function is
`𝒥(u) = ⌊2u⌋ u - ⌊2u⌋ (⌊2u⌋ + 1) / 4`.
On each interval `[k/2, (k+1)/2)` it is the affine function `k u - k (k+1) / 4`.

## Main definitions

* `Zeta5Irr.innerLimitingFunction`: the function `𝒥`.

## Main results

* `Zeta5Irr.innerLimitingFunction_of_floor_eq`: the affine formula on `[k/2, (k+1)/2)`.
* `Zeta5Irr.innerLimitingFunction_zero`: `𝒥(0) = 0`.
* `Zeta5Irr.innerLimitingFunction_nonneg`: `0 ≤ 𝒥(u)` for `u ≥ 0`.

## Implementation notes

* The function is defined on all of `ℝ`, with no hypothesis `0 ≤ u`; the source only uses it
  for `u ≥ 0`, and lemmas that need this assume it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The inner limiting function `𝒥(u) = ⌊2u⌋ u - ⌊2u⌋ (⌊2u⌋ + 1) / 4`. -/
@[zeta5irr "def_J"]
noncomputable def innerLimitingFunction (u : ℝ) : ℝ :=
  ⌊2 * u⌋ * u - ⌊2 * u⌋ * (⌊2 * u⌋ + 1) / 4

/-- If `⌊2u⌋ = k`, then `𝒥(u) = k u - k (k + 1) / 4`. -/
theorem innerLimitingFunction_of_floor_eq {u : ℝ} {k : ℤ} (h : ⌊2 * u⌋ = k) :
    innerLimitingFunction u = k * u - k * (k + 1) / 4 := by
  simp [innerLimitingFunction, h]

/-- `𝒥(0) = 0`. -/
@[simp]
theorem innerLimitingFunction_zero : innerLimitingFunction 0 = 0 := by
  simp [innerLimitingFunction]

/-- `𝒥` is nonnegative on `[0, ∞)`. -/
theorem innerLimitingFunction_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ innerLimitingFunction u := by
  set k : ℤ := ⌊2 * u⌋ with hk
  rw [innerLimitingFunction_of_floor_eq hk.symm]
  have hk0' : 0 ≤ k := Int.floor_nonneg.mpr (by linarith)
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk0'
  have hku : (k : ℝ) ≤ 2 * u := Int.floor_le _
  have hkk : (0 : ℝ) ≤ k * (k - 1) := by
    have : (0 : ℤ) ≤ k * (k - 1) := by
      rcases (show k = 0 ∨ 1 ≤ k by omega) with h | h
      · simp [h]
      · exact mul_nonneg (by omega) (by omega)
    exact_mod_cast this
  nlinarith [mul_le_mul_of_nonneg_left hku hk0]

end Zeta5Irr
