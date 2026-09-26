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
# The half-index `m° = (p - 1) / 2`

For an odd prime `p`, the paper writes `m° = (p - 1) / 2`; it is the number of nonzero square
classes modulo `p`, and is used as an index bound when working with square classes.

## Main definitions

* `Zeta5Irr.mStar`: the natural number `(p - 1) / 2`.

## Main results

* `Zeta5Irr.two_mul_mStar_add_one`: if `p` is odd then `2 * m° + 1 = p`.
* `Zeta5Irr.mStar_lt`: if `p` is odd then `m° < p`.
* `Zeta5Irr.one_le_mStar`: if `p` is odd and `3 ≤ p` then `1 ≤ m°`.
* `Nat.Prime.one_le_mStar`: if `p` is an odd prime then `1 ≤ m°`.

## Implementation notes

* `mStar` is defined for every natural number using truncated natural division, with no
  primality or oddness hypothesis; the source only uses it for odd primes, and the lemmas
  take oddness as a separate hypothesis.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

/-- The index `m° = (p - 1) / 2`. For an odd prime `p` this is the number of nonzero squares
modulo `p`. It is defined for all `p` via natural division. -/
@[zeta5irr "def_in_mstar"]
def mStar (p : ℕ) : ℕ := (p - 1) / 2

/-- Unfolding lemma for `mStar`. -/
theorem mStar_def (p : ℕ) : mStar p = (p - 1) / 2 := rfl

/-- For odd `p`, `2 * m° + 1 = p`. -/
theorem two_mul_mStar_add_one {p : ℕ} (hp : Odd p) : 2 * mStar p + 1 = p := by
  obtain ⟨k, rfl⟩ := hp
  simp [mStar]

/-- For odd `p`, `m° = p / 2`. -/
theorem mStar_eq_div_two {p : ℕ} (hp : Odd p) : mStar p = p / 2 := by
  obtain ⟨k, rfl⟩ := hp
  simp [mStar]
  omega

/-- For odd `p`, `m° < p`. -/
theorem mStar_lt {p : ℕ} (hp : Odd p) : mStar p < p := by
  have := two_mul_mStar_add_one hp
  omega

/-- For odd `p ≥ 3`, `1 ≤ m°`. -/
theorem one_le_mStar {p : ℕ} (hp : Odd p) (h3 : 3 ≤ p) : 1 ≤ mStar p := by
  have := two_mul_mStar_add_one hp
  omega

/-- For an odd prime `p`, `1 ≤ m°`. -/
theorem _root_.Nat.Prime.one_le_mStar {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 1 ≤ mStar p :=
  Zeta5Irr.one_le_mStar hodd <| by
    have := hp.two_le
    obtain ⟨k, rfl⟩ := hodd
    omega

end Zeta5Irr
