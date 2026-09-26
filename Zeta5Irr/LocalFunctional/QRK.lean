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
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The punctured symmetric interval `R_K`

For a natural number `K`, the set `R_K = {s ∈ ℤ : -K ≤ s ≤ K, s ≠ 0}` is the integer interval
`[-K, K]` with `0` removed. It has `2K` elements.

## Main definitions

* `Zeta5Irr.puncturedIcc`: the finite set `R_K`.

## Main results

* `Zeta5Irr.mem_puncturedIcc`: `s ∈ R_K ↔ s ≠ 0 ∧ -K ≤ s ∧ s ≤ K`.
* `Zeta5Irr.card_puncturedIcc`: `#R_K = 2K`.

## Implementation notes

* `R_K` is a `Finset ℤ` rather than a `Set ℤ`, since it is summed and multiplied over and its
  elements are counted.
* The source assumes `K ≥ 1`; the definition makes sense for every `K : ℕ`, and `R_0 = ∅`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6: small primes.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The punctured symmetric interval `R_K = {s ∈ ℤ : -K ≤ s ≤ K, s ≠ 0}`, a set of `2K`
integers. -/
@[zeta5irr "def_qRK"]
def puncturedIcc (K : ℕ) : Finset ℤ :=
  (Icc (-(K : ℤ)) K).erase 0

/-- Membership in `R_K`. -/
@[simp]
theorem mem_puncturedIcc {K : ℕ} {s : ℤ} :
    s ∈ puncturedIcc K ↔ s ≠ 0 ∧ -(K : ℤ) ≤ s ∧ s ≤ K := by
  simp [puncturedIcc]

/-- The elements of `R_K` are nonzero. -/
theorem ne_zero_of_mem_puncturedIcc {K : ℕ} {s : ℤ} (hs : s ∈ puncturedIcc K) : s ≠ 0 :=
  (mem_puncturedIcc.1 hs).1

/-- `0 ∉ R_K`. -/
@[simp]
theorem zero_notMem_puncturedIcc (K : ℕ) : (0 : ℤ) ∉ puncturedIcc K := by
  simp

/-- The elements of `R_K` have absolute value at most `K`. -/
theorem abs_le_of_mem_puncturedIcc {K : ℕ} {s : ℤ} (hs : s ∈ puncturedIcc K) : |s| ≤ K :=
  abs_le.2 (mem_puncturedIcc.1 hs).2

/-- `R_K` is closed under negation. -/
theorem neg_mem_puncturedIcc {K : ℕ} {s : ℤ} (hs : s ∈ puncturedIcc K) :
    -s ∈ puncturedIcc K := by
  rw [mem_puncturedIcc] at hs ⊢
  omega

/-- `R_K` has `2K` elements. -/
@[simp]
theorem card_puncturedIcc (K : ℕ) : #(puncturedIcc K) = 2 * K := by
  rw [puncturedIcc, card_erase_of_mem (by simp), Int.card_Icc]
  omega

end Zeta5Irr
