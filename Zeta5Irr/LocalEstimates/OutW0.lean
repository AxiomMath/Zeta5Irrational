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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
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
# The entry valuations `w_{0,i}` of the outer range

For a prime `p`, write `m_A = ⌊A / p⌋`. In the outer range the block `a = 0` has
`m_K - m_N` rows, and `m_K - m_N ∈ {1, 2}`. For `0 ≤ i < m_K - m_N` the entry valuations of
this block are
`w_{0,i} = -1/2` if `m_K - m_N = 1`, and `w_{0,i} = 2 i - 2` if `m_K - m_N = 2`.

## Main definitions

* `Zeta5Irr.outerWeightZero`: the entry valuation `w_{0,i}`.

## Main results

* `Zeta5Irr.outerWeightZero_of_sub_eq_one`: `w_{0,i} = -1/2` when `m_K - m_N = 1`.
* `Zeta5Irr.outerWeightZero_of_sub_eq_two`: `w_{0,i} = 2 i - 2` when `m_K - m_N = 2`.
* `Zeta5Irr.outerWeightZero_ne_zero_of_sub_eq_one`: no entry vanishes when `m_K - m_N = 1`.
* `Zeta5Irr.outerWeightZero_eq_zero_iff_of_sub_eq_two`: when `m_K - m_N = 2`, `w_{0,i} = 0`
  if and only if `i = 1`.

## Implementation notes

* The quotients `m_K` and `m_N` are explicit natural-number arguments; callers pass
  `mA p K` and `mA p N`. The prime `p` enters only through them.
* The value is rational because of the branch `-1/2`.
* The source only defines `w_{0,i}` for `m_K - m_N ∈ {1, 2}` and `i < m_K - m_N`. Outside the
  case `m_K - m_N = 1` the formula `2 i - 2` is used, so the definition is total; the lemmas
  carry the hypothesis selecting the case they describe.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10: the outer range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

/-- The entry valuation `w_{0,i}` of the block `a = 0` of the outer range: `-1/2` if
`m_K - m_N = 1`, and `2 i - 2` otherwise (the source's case `m_K - m_N = 2`). -/
@[zeta5irr "def_out_w0"]
def outerWeightZero (mK mN i : ℕ) : ℚ :=
  if mK - mN = 1 then -1 / 2 else 2 * i - 2

/-- `w_{0,i} = -1/2` when `m_K - m_N = 1`. -/
theorem outerWeightZero_of_sub_eq_one {mK mN : ℕ} (h : mK - mN = 1) (i : ℕ) :
    outerWeightZero mK mN i = -1 / 2 := by
  simp [outerWeightZero, h]

/-- `w_{0,i} = 2 i - 2` when `m_K - m_N = 2`. -/
theorem outerWeightZero_of_sub_eq_two {mK mN : ℕ} (h : mK - mN = 2) (i : ℕ) :
    outerWeightZero mK mN i = 2 * i - 2 := by
  simp [outerWeightZero, h]

/-- No entry valuation vanishes when `m_K - m_N = 1`. -/
theorem outerWeightZero_ne_zero_of_sub_eq_one {mK mN : ℕ} (h : mK - mN = 1) (i : ℕ) :
    outerWeightZero mK mN i ≠ 0 := by
  rw [outerWeightZero_of_sub_eq_one h]
  norm_num

/-- When `m_K - m_N = 2`, the entry valuation `w_{0,i}` vanishes exactly for `i = 1`. -/
theorem outerWeightZero_eq_zero_iff_of_sub_eq_two {mK mN : ℕ} (h : mK - mN = 2) {i : ℕ} :
    outerWeightZero mK mN i = 0 ↔ i = 1 := by
  rw [outerWeightZero_of_sub_eq_two h, sub_eq_zero]
  constructor
  · intro hi
    exact_mod_cast (by linarith : (i : ℚ) = 1)
  · rintro rfl
    norm_num

end Zeta5Irr
