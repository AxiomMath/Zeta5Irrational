/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
# Accuracy of the truncated logarithm series

For `0 ≤ z ≤ 1/3` the quantity `2 z^129 / (129 (1 - z^2))`, which bounds the tail of the series
`log ((1 + z) / (1 - z)) = 2 ∑ z^{2k+1} / (2k+1)` truncated after the `z^127` term, is smaller
than `2^{-144}`. Indeed `z^129 ≤ 3^{-129}` and `1 - z^2 ≥ 8/9`, so the quantity is at most
`(18 / 1032) 3^{-129} < 3^{-129}`, and `3^{129} > 2^{144}` since `3^2 > 2^3`.

## Main results

* `Zeta5Irr.two_mul_pow_129_div_lt`: for `0 ≤ z ≤ 1/3`,
  `2 z^129 / (129 (1 - z^2)) < 2^{-144}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

/-- For `0 ≤ z ≤ 1/3`, `2 z^129 / (129 (1 - z^2)) < 2^{-144}`. -/
@[zeta5irr "lem_enc_log_acc"]
theorem two_mul_pow_129_div_lt {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z ≤ 1 / 3) :
    2 * z ^ 129 / (129 * (1 - z ^ 2)) < (2 : ℝ) ^ (-144 : ℤ) := by
  have hz2 : z ^ 2 ≤ 1 / 9 := by nlinarith
  have hpow : z ^ 129 ≤ (1 / 3 : ℝ) ^ 129 := pow_le_pow_left₀ h₀ h₁ 129
  calc 2 * z ^ 129 / (129 * (1 - z ^ 2)) ≤ 2 * (1 / 3 : ℝ) ^ 129 / (129 * (8 / 9)) := by
        gcongr
        linarith
    _ < (2 : ℝ) ^ (-144 : ℤ) := by norm_num

end Zeta5Irr
