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
# The outer rank bound `r_p`

For a prime `p` and the parameters `K` and `N` of the construction, the outer rank bound is
`r_p = max(0, K + 4 N - 2 p + 2)`.
In the outer range the Hankel matrix splits `p`-adically as `G_K = A + p⁻¹ L` with `A` and `L`
integral, and `r_p` bounds the rank of the correction `L` over `ℚ_p`; it enters the local
estimate at `p` through the rank correction `min(r_p, ·)`.

## Main definitions

* `Zeta5Irr.outerRankBound`: the outer rank bound `r_p = max(0, K + 4 N - 2 p + 2)`.

## Main results

* `Zeta5Irr.outerRankBound_eq_max`: `r_p = max(0, K + 4 N + 2 - 2 p)` in `ℕ`.
* `Zeta5Irr.cast_outerRankBound`: `r_p = max(0, K + 4 N - 2 p + 2)` in `ℤ`, the form of the
  source.
* `Zeta5Irr.le_outerRankBound`: `K + 4 N - 2 p + 2 ≤ r_p` in `ℤ`.
* `Zeta5Irr.outerRankBound_eq_zero_iff`: `r_p = 0` if and only if `K + 4 N + 2 ≤ 2 p`.
* `Zeta5Irr.outerRankBound_add_two_mul`: `r_p + 2 p = K + 4 N + 2` when `2 p ≤ K + 4 N + 2`.

## Implementation notes

* The bound is valued in `ℕ`, because it is compared with the rank of a matrix, and the
  maximum with `0` is realised by truncated subtraction: `r_p = K + 4 N + 2 - 2 p`. The source's
  integer form is `cast_outerRankBound`.
* The source fixes `K = 40 n` and `N = 3 n`; here `K` and `N` are arbitrary natural numbers.
  It also takes `p` prime, which the definition does not use, so `p` is any natural number.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4, equation (4.10): the rank bound in the outer range.
-/

@[expose] public section

namespace Zeta5Irr

/-- The outer rank bound `r_p = max(0, K + 4 N - 2 p + 2)`, written with truncated subtraction
as `K + 4 N + 2 - 2 p`. It bounds the `ℚ_p`-rank of the correction `L` in the splitting
`G_K = A + p⁻¹ L` of the outer range. -/
@[zeta5irr "def_rp"]
def outerRankBound (K N p : ℕ) : ℕ := K + 4 * N + 2 - 2 * p

variable {K N p : ℕ}

/-- The outer rank bound is `max(0, K + 4 N + 2 - 2 p)` in `ℕ`. -/
theorem outerRankBound_eq_max (K N p : ℕ) :
    outerRankBound K N p = max 0 (K + 4 * N + 2 - 2 * p) := by
  simp [outerRankBound]

/-- The outer rank bound is `max(0, K + 4 N - 2 p + 2)` in `ℤ`. -/
theorem cast_outerRankBound (K N p : ℕ) :
    (outerRankBound K N p : ℤ) = max 0 ((K : ℤ) + 4 * N - 2 * p + 2) := by
  unfold outerRankBound
  omega

/-- `K + 4 N - 2 p + 2 ≤ r_p` in `ℤ`. -/
theorem le_outerRankBound (K N p : ℕ) :
    (K : ℤ) + 4 * N - 2 * p + 2 ≤ outerRankBound K N p := by
  rw [cast_outerRankBound]
  exact le_max_right _ _

/-- The outer rank bound vanishes exactly when `K + 4 N + 2 ≤ 2 p`. -/
theorem outerRankBound_eq_zero_iff : outerRankBound K N p = 0 ↔ K + 4 * N + 2 ≤ 2 * p := by
  simp [outerRankBound, Nat.sub_eq_zero_iff_le]

/-- When `2 p ≤ K + 4 N + 2`, the outer rank bound satisfies `r_p + 2 p = K + 4 N + 2`. -/
theorem outerRankBound_add_two_mul (h : 2 * p ≤ K + 4 * N + 2) :
    outerRankBound K N p + 2 * p = K + 4 * N + 2 := by
  unfold outerRankBound
  omega

end Zeta5Irr
