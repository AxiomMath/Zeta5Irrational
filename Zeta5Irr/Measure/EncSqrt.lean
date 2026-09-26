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
# A rational lower enclosure of the square root

For a rational `x ≥ 0`, the enclosure of `√x` at precision `2^{-144}` is
`s(x) = 2^{-144} max {n ∈ ℤ_{≥0} : n² ≤ 2^{288} x}`.
The maximum is the integer square root of `⌊2^{288} x⌋`, since for a natural number `n`
the inequality `n² ≤ 2^{288} x` holds iff `n² ≤ ⌊2^{288} x⌋`.

## Main definitions

* `Zeta5Irr.sqrtApprox`: the enclosure `s(x)`.

## Main results

* `Zeta5Irr.sq_le_iff_le_sqrtApproxNum`: for natural `n`, `n² ≤ 2^{288} x` iff `n` is at most
  the numerator `2^{144} s(x)`.
* `Zeta5Irr.isGreatest_sqrtApproxNum`: for `x ≥ 0`, the numerator `2^{144} s(x)` is the
  greatest `n` with `n² ≤ 2^{288} x`, so `s(x)` is the blueprint's quantity.
* `Zeta5Irr.sqrtApprox_eq`: `s(x) = 2^{-144} n` for that greatest `n`.
* `Zeta5Irr.sqrtApprox_nonneg`: `0 ≤ s(x)`.

## Implementation notes

* The enclosure is defined through `Nat.sqrt` and `Nat.floor`, which is the construction
  of `Nat.ratSqrt` extended to rational arguments at the fixed precision `2^{144}`.
* It is a total function `ℚ → ℚ`: for `x < 0` the floor is `0` and `s(x) = 0`. The
  characterisation as a maximum is stated for `x ≥ 0`, as in the source.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

/-- The numerator of the square-root enclosure: `⌊√⌊2^{288} x⌋⌋`, the greatest natural
number `n` with `n² ≤ 2^{288} x` when `x ≥ 0`. -/
def sqrtApproxNum (x : ℚ) : ℕ :=
  Nat.sqrt ⌊(2 : ℚ) ^ 288 * x⌋₊

/-- The rational enclosure of the square root at precision `2^{-144}`:
`s(x) = 2^{-144} max {n ∈ ℤ_{≥0} : n² ≤ 2^{288} x}`. -/
@[zeta5irr "def_enc_sqrt"]
def sqrtApprox (x : ℚ) : ℚ :=
  (sqrtApproxNum x : ℚ) / 2 ^ 144

/-- For natural `n`, `n² ≤ 2^{288} x` iff `n ≤ 2^{144} s(x)`. -/
theorem sq_le_iff_le_sqrtApproxNum {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    ((n : ℚ) ^ 2 ≤ 2 ^ 288 * x) ↔ n ≤ sqrtApproxNum x := by
  rw [sqrtApproxNum, Nat.le_sqrt, Nat.le_floor_iff (by positivity), sq]
  push_cast
  rfl

/-- For `x ≥ 0`, the numerator `2^{144} s(x)` is the greatest natural number `n` with
`n² ≤ 2^{288} x`. -/
theorem isGreatest_sqrtApproxNum {x : ℚ} (hx : 0 ≤ x) :
    IsGreatest {n : ℕ | (n : ℚ) ^ 2 ≤ 2 ^ 288 * x} (sqrtApproxNum x) :=
  ⟨(sq_le_iff_le_sqrtApproxNum hx _).2 le_rfl,
    fun _ hn => (sq_le_iff_le_sqrtApproxNum hx _).1 hn⟩

/-- For `x ≥ 0`, `s(x) = 2^{-144} n` where `n` is the greatest natural number with
`n² ≤ 2^{288} x`. -/
theorem sqrtApprox_eq {x : ℚ} (hx : 0 ≤ x) {n : ℕ}
    (hn : IsGreatest {n : ℕ | (n : ℚ) ^ 2 ≤ 2 ^ 288 * x} n) :
    sqrtApprox x = (2 : ℚ) ^ (-144 : ℤ) * n := by
  rw [sqrtApprox, (isGreatest_sqrtApproxNum hx).unique hn, div_eq_inv_mul]
  norm_num

/-- The square-root enclosure is nonnegative. -/
theorem sqrtApprox_nonneg (x : ℚ) : 0 ≤ sqrtApprox x := by
  unfold sqrtApprox
  positivity

end Zeta5Irr
