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
# Accuracy of the truncated arctangent series

For `0 ≤ z ≤ 1/2` the term `z^161 / 161`, which bounds the tail of the arctangent series
truncated after the `z^159` term, is smaller than `2^{-144}`. Indeed `z^161 ≤ 2^{-161}`, and
dividing by `161 > 1` gives `z^161 / 161 < 2^{-161} < 2^{-144}`.

## Main results

* `Zeta5Irr.pow_161_div_161_lt`: for `0 ≤ z ≤ 1/2`, `z^161 / 161 < 2^{-144}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

/-- For `0 ≤ z ≤ 1/2`, `z^161 / 161 < 2^{-144}`. -/
@[zeta5irr "lem_enc_atan_acc"]
theorem pow_161_div_161_lt {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z ≤ 1 / 2) :
    z ^ 161 / 161 < (2 : ℝ) ^ (-144 : ℤ) := by
  have h : z ^ 161 ≤ (1 / 2 : ℝ) ^ 161 := pow_le_pow_left₀ h₀ h₁ 161
  calc z ^ 161 / 161 ≤ (1 / 2 : ℝ) ^ 161 / 161 := by gcongr
    _ < (2 : ℝ) ^ (-144 : ℤ) := by norm_num

end Zeta5Irr
