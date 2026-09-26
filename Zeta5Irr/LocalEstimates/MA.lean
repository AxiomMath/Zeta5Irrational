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
# The quotient `m_A`

For a prime `p` and an integer `A ≥ 0`, the source sets `m_A = ⌊A / p⌋`, the number of multiples
of `p` in `{1, …, A}`.

## Main definitions

* `Zeta5Irr.mA`: the quotient `m_A = ⌊A / p⌋`.

## Main results

* `Zeta5Irr.mA_eq_floor`: `m_A` is the floor of the real quotient `A / p`.
* `Zeta5Irr.mA_eq_intFloor`: `m_A` is the integer floor of the real quotient `A / p`.

## Implementation notes

* `m_A` is an `abbrev` for truncated natural division `A / p`, so that Mathlib's lemmas about
  `Nat.div` (`Nat.div_add_mod`, `Nat.lt_div_iff_mul_lt`, …) apply to it directly.
* The source takes `p` prime; primality is not needed to define `m_A`, so `p` is an arbitrary
  natural number here (with `A / 0 = 0`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

/-- The quotient `m_A = ⌊A / p⌋`, as truncated natural division. -/
@[zeta5irr "def_mA"]
abbrev mA (p A : ℕ) : ℕ :=
  A / p

/-- `m_A` is the (natural) floor of the quotient `A / p` in any linearly ordered semifield. -/
theorem mA_eq_floor {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    [FloorSemiring α] (p A : ℕ) : mA p A = ⌊(A : α) / p⌋₊ :=
  (Nat.floor_div_eq_div A p).symm

/-- `m_A` is the integer floor of the quotient `A / p` in any linearly ordered field. -/
theorem mA_eq_intFloor {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [FloorRing α] (p A : ℕ) : (mA p A : ℤ) = ⌊(A : α) / p⌋ := by
  rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]

end Zeta5Irr
