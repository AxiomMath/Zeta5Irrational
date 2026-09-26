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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# An upper bound for `log (m !)`

For every natural number `m`,
`log (m !) ≤ m log m - m + log m + 1`.
This is the upper half of the elementary factorial bounds used to control the scaling of the
Gram integral.

## Main results

* `Zeta5Irr.log_factorial_le_half`: the sharper bound `log (m !) ≤ m log m - m + (log m) / 2 + 1`.
* `Zeta5Irr.log_factorial_le`: `log (m !) ≤ m log m - m + log m + 1`.

## Implementation notes

The source compares `∑_{j < m} log j` with `∫_1^m log x dx`. Here the bound is instead read off
from the Stirling sequence `s(n) = n! / (√(2n) (n/e)^n)`: it is antitone on `n ≥ 1` and
`s(1) = e / √2`, so `log s(m) ≤ log s(1)`, which unfolds to the sharper bound with `(log m) / 2`
in place of `log m`. The claimed bound follows since `log m ≥ 0`. Both statements hold for
every `m : ℕ`, the case `m = 0` being `0 ≤ 1` under the convention `log 0 = 0`, so the source's
hypothesis `m ≥ 1` is dropped.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §"The Gram integral and scaling".
-/

@[expose] public section

namespace Zeta5Irr

open Real Stirling

/-- The Stirling-type upper bound `log (m !) ≤ m log m - m + (log m) / 2 + 1`, valid for every
natural number `m`. -/
theorem log_factorial_le_half (m : ℕ) :
    Real.log m.factorial ≤ m * Real.log m - m + Real.log m / 2 + 1 := by
  rcases m with _ | n
  · simp
  have h1 : Real.log (stirlingSeq (n + 1)) ≤ Real.log (stirlingSeq 1) :=
    log_stirlingSeq'_antitone (Nat.zero_le n)
  have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [log_stirlingSeq_formula, log_stirlingSeq_formula, Real.log_mul two_ne_zero hpos.ne',
    Real.log_div hpos.ne' (exp_pos 1).ne', Real.log_exp] at h1
  simp only [Nat.factorial_one, Nat.cast_one, Real.log_one, mul_one,
    Real.log_div one_ne_zero (exp_pos 1).ne', Real.log_exp] at h1
  push_cast at h1 ⊢
  linarith

/-- **Upper factorial bound.** For every natural number `m`,
`log (m !) ≤ m log m - m + log m + 1`. -/
@[zeta5irr "lem_factorial_bounds"]
theorem log_factorial_le (m : ℕ) :
    Real.log m.factorial ≤ m * Real.log m - m + Real.log m + 1 := by
  have := log_factorial_le_half m
  have : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  linarith

end Zeta5Irr
