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
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
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
# A lower bound for `log (m!)`

For every integer `m ≥ 1` we have `m log m - m + 1 ≤ log (m!)`. This is the elementary lower
bound comparing `∑_{j=2}^m log j` with `∫_1^m log x dx = m log m - m + 1`.

## Main results

* `Zeta5Irr.mul_log_sub_add_one_le_log_factorial`: `m log m - m + 1 ≤ log (m!)` for `m ≥ 1`.

## Implementation notes

The source compares the sum with the integral of the monotone function `log` on `[1, m]`. We
instead deduce the bound from the sharper Stirling lower bound
`m log m - m + (log m)/2 + (log 2π)/2 ≤ log (m!)` (`Stirling.le_log_factorial_stirling`): for
`m ≥ 2` one has `2πm ≥ 4π > e²`, so `(log m)/2 + (log 2π)/2 ≥ 1`. The case `m = 1`, where both
sides vanish, is checked directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9 (the Gram integral and scaling).
-/

@[expose] public section

namespace Zeta5Irr

open Nat

/-- For every integer `m ≥ 1`, `m log m - m + 1 ≤ log (m!)`. -/
@[zeta5irr "lem_real_factorial_lower"]
theorem mul_log_sub_add_one_le_log_factorial {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m + 1 ≤ Real.log (m ! : ℝ) := by
  obtain rfl | hm2 : m = 1 ∨ 2 ≤ m := by omega
  · simp
  have hS := Stirling.le_log_factorial_stirling (n := m) (by omega)
  have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have key : (2 : ℝ) ≤ Real.log (m * (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.pi_gt_three]
  rw [Real.log_mul (by positivity) (by positivity)] at key
  linarith

end Zeta5Irr
