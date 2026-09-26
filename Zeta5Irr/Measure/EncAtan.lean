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
# Truncated arctangent series

For `m : ℕ` and `z` in a division ring, the `m`-th partial sum of the Taylor series of the
arctangent at `0` is
`T_m(z) = ∑_{k=0}^{m-1} (-1)^k z^{2k+1} / (2k+1)`.
These partial sums give elementary rational enclosures of `arctan z` for small `z`.

## Main definitions

* `Zeta5Irr.atanApprox`: the truncated arctangent series `T_m`.

## Main results

* `Zeta5Irr.atanApprox_zero`, `Zeta5Irr.atanApprox_succ`: the recursion in `m`.
* `Zeta5Irr.map_atanApprox`, `Zeta5Irr.Rat.cast_atanApprox`: `T_m` commutes with ring
  homomorphisms of division rings, in particular with the cast `ℚ → ℝ`.
* `Zeta5Irr.atanApprox_neg`: `T_m` is odd.

## Implementation notes

* The source defines `T_m` for real `z` and `m ≥ 1`. Here `z` ranges over any division ring,
  so that `T_m` of a rational argument is a computable rational number, which casts to the
  real value by `Zeta5Irr.Rat.cast_atanApprox`. The case `m = 0` is allowed and gives the
  empty sum `0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

variable {K L : Type*} [DivisionRing K] [DivisionRing L]

/-- The truncated arctangent series `T_m(z) = ∑_{k=0}^{m-1} (-1)^k z^{2k+1} / (2k+1)`. -/
@[zeta5irr "def_enc_atan"]
def atanApprox (m : ℕ) (z : K) : K :=
  ∑ k ∈ range m, (-1) ^ k * z ^ (2 * k + 1) / (2 * k + 1)

/-- The empty truncation is `0`. -/
@[simp]
theorem atanApprox_zero (z : K) : atanApprox 0 z = 0 := by
  simp [atanApprox]

/-- One more term of the arctangent series. -/
theorem atanApprox_succ (m : ℕ) (z : K) :
    atanApprox (m + 1) z = atanApprox m z + (-1) ^ m * z ^ (2 * m + 1) / (2 * m + 1) := by
  simp [atanApprox, sum_range_succ]

/-- The first truncation is `T_1(z) = z`. -/
@[simp]
theorem atanApprox_one (z : K) : atanApprox 1 z = z := by
  simp [atanApprox]

/-- The truncated arctangent series commutes with ring homomorphisms. -/
theorem map_atanApprox {F : Type*} [FunLike F K L] [RingHomClass F K L] (f : F) (m : ℕ)
    (z : K) : f (atanApprox m z) = atanApprox m (f z) := by
  simp [atanApprox, map_sum, map_div₀, map_ofNat]

/-- The truncated arctangent series commutes with the cast from `ℚ`. -/
@[simp, norm_cast]
theorem Rat.cast_atanApprox [CharZero K] (m : ℕ) (q : ℚ) :
    ((atanApprox m q : ℚ) : K) = atanApprox m (q : K) :=
  map_atanApprox (Rat.castHom K) m q

/-- The truncated arctangent series is an odd function. -/
theorem atanApprox_neg (m : ℕ) (z : K) : atanApprox m (-z) = -atanApprox m z := by
  simp only [atanApprox, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [Odd.neg_pow ⟨k, rfl⟩, mul_neg, neg_div]

end Zeta5Irr
