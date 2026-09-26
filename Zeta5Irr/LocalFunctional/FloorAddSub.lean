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
# A floor inequality for `K + r` and `K - r`

For integers `n ≥ 1`, `K` and `r`,
`⌊(K + r)/n⌋ + ⌊(K - r)/n⌋ ≤ 2⌊K/n⌋ + 1`.
Indeed `⌊a/n⌋ + ⌊b/n⌋ ≤ ⌊(a + b)/n⌋`, so the left side is at most `⌊2K/n⌋`, and writing
`K = qn + ρ` with `0 ≤ ρ < n` gives `⌊2K/n⌋ ≤ 2q + 1`. This bounds the exponent of a small prime
in a ratio of factorials appearing in the local functional.

## Main results

* `Zeta5Irr.add_ediv_add_sub_ediv_le`: `(K + r) / n + (K - r) / n ≤ 2 * (K / n) + 1`.

## Implementation notes

The floor `⌊x/n⌋` of the source is the Euclidean division `x / n` on `ℤ`, which agrees with it
for `n > 0`. The source assumes `n ≥ 1`, `K ≥ 0` and `0 ≤ r ≤ K`; none of these hypotheses is
needed. The inequality holds for all integers `n`, `K`, `r`: for `n = 0` both sides are `0` and
`1`, and for `n < 0` one has `x / n = -(x / (-n))`, so it reduces to the lower bound
`⌊a/m⌋ + ⌊b/m⌋ ≥ ⌊(a + b)/m⌋ - 1` for `m = -n > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

/-- For all integers `n`, `K`, `r`, `⌊(K + r)/n⌋ + ⌊(K - r)/n⌋ ≤ 2⌊K/n⌋ + 1`, where `/` is the
Euclidean division on `ℤ` (the floor of the quotient when `n > 0`). -/
@[zeta5irr "lem_small_floor"]
theorem add_ediv_add_sub_ediv_le (n K r : ℤ) :
    (K + r) / n + (K - r) / n ≤ 2 * (K / n) + 1 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨m, hm, rfl⟩ : ∃ m, 0 < m ∧ n = -m := ⟨-n, by omega, by ring⟩
    simp only [Int.ediv_neg]
    have h₁ := Int.mul_ediv_add_emod (K + r) m
    have h₂ := Int.mul_ediv_add_emod (K - r) m
    have h₃ := Int.mul_ediv_add_emod K m
    have e₁ := Int.emod_lt_of_pos (K + r) hm
    have e₂ := Int.emod_lt_of_pos (K - r) hm
    have e₃ := Int.emod_nonneg K hm.ne'
    have : m * (2 * (K / m) - 2) < m * ((K + r) / m + (K - r) / m) := by nlinarith
    have := lt_of_mul_lt_mul_left this hm.le
    omega
  · simp
  · have h₁ := Int.mul_ediv_add_emod (K + r) n
    have h₂ := Int.mul_ediv_add_emod (K - r) n
    have h₃ := Int.mul_ediv_add_emod K n
    have e₁ := Int.emod_lt_of_pos K hn
    have e₂ := Int.emod_nonneg (K + r) hn.ne'
    have e₃ := Int.emod_nonneg (K - r) hn.ne'
    have : n * ((K + r) / n + (K - r) / n) < n * (2 * (K / n) + 2) := by nlinarith
    have := lt_of_mul_lt_mul_left this hn.le
    omega

end Zeta5Irr
