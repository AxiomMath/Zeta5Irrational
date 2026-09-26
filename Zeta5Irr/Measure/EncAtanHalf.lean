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
public import Mathlib.Tactic.ENatToNat
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
# The half-angle formula for the arctangent

For every real `x`,
`arctan x = 2 arctan (x / (1 + √(1 + x²)))`.
With `s = √(1 + x²)` and `u = x / (1 + s)` one has `|u| < 1` and
`1 - u² = 2 / (1 + s)`, so the double-angle formula
`2 arctan u = arctan (2u / (1 - u²))` gives the claim, since `2u / (1 - u²) = x`.

## Main results

* `Zeta5Irr.arctan_eq_two_mul_arctan_div_one_add_sqrt`: the half-angle formula.

## Implementation notes

* The source states the identity for `0 ≤ x ≤ 1`; it holds for every real `x`, since
  `|x| < 1 + √(1 + x²)` always, and it is stated here in that generality.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

/-- The half-angle formula for the arctangent: `arctan x = 2 arctan (x / (1 + √(1 + x²)))`
for every real `x`. -/
@[zeta5irr "lem_enc_atan_half"]
theorem arctan_eq_two_mul_arctan_div_one_add_sqrt (x : ℝ) :
    Real.arctan x = 2 * Real.arctan (x / (1 + √(1 + x ^ 2))) := by
  set s := √(1 + x ^ 2)
  have hs2 : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < 1 + s := by linarith [Real.sqrt_nonneg (1 + x ^ 2)]
  have habs : |x| < 1 + s := by
    have : |x| ≤ s := Real.abs_le_sqrt (by nlinarith)
    linarith
  rw [Real.two_mul_arctan]
  · congr 1
    have key : (1 + s) ^ 2 - x ^ 2 = 2 * (1 + s) := by linear_combination hs2
    rw [div_pow, one_sub_div (by positivity), key]
    field_simp
  · rw [lt_div_iff₀ hpos]
    linarith [neg_abs_le x]
  · rw [div_lt_iff₀ hpos]
    linarith [le_abs_self x]

end Zeta5Irr
