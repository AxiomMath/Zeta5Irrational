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
# The size of the near-pole quotient

Let `M ≥ 1` and `K` be integers and `p > K / M`. If `0 ≤ σ < p` and `r` is an integer with
`|r| ≤ K` and `r ≡ σ [ZMOD p]`, then `(r - σ) / p` is an integer of absolute value at most `M`.
Indeed `|r - σ| ≤ |r| + σ ≤ K + p - 1 < p M + p`, so the integer `(r - σ) / p` has absolute
value strictly less than `M + 1`.

## Main results

* `Zeta5Irr.abs_sub_div_le_of_modEq`: `p ∣ r - σ` and `|(r - σ) / p| ≤ M`.

## Implementation notes

* The quotient is the integer division `(r - σ) / p`; the first conjunct `p ∣ r - σ` says this
  division is exact, i.e. that the rational number `(r - σ) / p` is an integer.
* The source's hypotheses `K ≥ 1` and `p` prime are not needed and are dropped; `M ≥ 1` is
  kept, as `0 < M`, so that `K / M` has its intended meaning.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5: the inner range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

/-- **The near-pole quotient is small.** If `0 < M`, `K / M < p`, `0 ≤ σ < p`, `|r| ≤ K` and
`r ≡ σ [ZMOD p]`, then `(r - σ) / p` is an integer (the division is exact) of absolute value
at most `M`. -/
@[zeta5irr "lem_in_nearpole_size"]
theorem abs_sub_div_le_of_modEq {M K p : ℕ} (hM : 0 < M) (hp : (K : ℝ) / M < p)
    {σ r : ℤ} (hσ₀ : 0 ≤ σ) (hσp : σ < p) (hr : |r| ≤ K) (hrσ : r ≡ σ [ZMOD p]) :
    (p : ℤ) ∣ r - σ ∧ |(r - σ) / p| ≤ M := by
  have hKp : (K : ℤ) < p * M := by
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    rw [div_lt_iff₀ hM'] at hp
    exact_mod_cast hp
  have hdvd : (p : ℤ) ∣ r - σ := (Int.ModEq.dvd hrσ.symm)
  refine ⟨hdvd, ?_⟩
  obtain ⟨n, hn⟩ := hdvd
  have hp0 : (0 : ℤ) < p := lt_of_le_of_lt hσ₀ hσp
  rw [hn, Int.mul_ediv_cancel_left _ hp0.ne']
  have h1 : |r - σ| ≤ |r| + σ := by
    have := abs_sub r σ
    rwa [abs_of_nonneg hσ₀] at this
  rw [hn, abs_mul, abs_of_pos hp0] at h1
  have h2 : (p : ℤ) * |n| < p * (M + 1) := by linarith
  have h3 : |n| < M + 1 := lt_of_mul_lt_mul_left h2 hp0.le
  omega

end Zeta5Irr
