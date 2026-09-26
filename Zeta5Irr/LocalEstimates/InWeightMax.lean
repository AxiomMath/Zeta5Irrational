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
# A maximum bound for sums of nonpositive half-integer weights

Let `w₁, …, w_h` be nonpositive half-integers, let `z` be the number of indices `r` with
`w_r = 0`, and let `r₀` be a natural number. For every `k ≤ min(r₀, h)` and every set `J` of
`k` indices,
`k + 2 ∑_{r ∈ J} w_r ≤ min(r₀, z)`.

## Main results

* `Zeta5Irr.card_add_two_mul_sum_le_min`: the bound `k + 2 ∑_{r ∈ J} w_r ≤ min(r₀, z)`.

## Implementation notes

* The source orders the weights decreasingly and studies the partial sums. We argue directly:
  split `J` into the indices with `w_r = 0` and those with `w_r ≠ 0`. Each nonzero
  nonpositive half-integer is at most `-1/2`, so `k + 2 ∑_{r ∈ J} w_r` is at most the number
  of zero weights in `J`, which is at most both `k ≤ r₀` and `z`.
* Half-integrality of `w_r` is expressed as `∃ n : ℤ, w_r = n / 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.1: valuation and determinant preliminaries.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- Let `w₁, …, w_h` be nonpositive half-integers, `z = #{r : w_r = 0}`, and `r₀ ∈ ℕ`. Then for
every `k ≤ min(r₀, h)` and every `J ⊆ {1, …, h}` with `#J = k`,
`k + 2 ∑_{r ∈ J} w_r ≤ min(r₀, z)`. -/
@[zeta5irr "lem_in_weight_max"]
theorem card_add_two_mul_sum_le_min {h : ℕ} (w : Fin h → ℝ) (hw_nonpos : ∀ r, w r ≤ 0)
    (hw_half : ∀ r, ∃ n : ℤ, w r = n / 2) (r₀ k : ℕ) (hk : k ≤ min r₀ h)
    (J : Finset (Fin h)) (hJ : #J = k) :
    (k : ℝ) + 2 * ∑ r ∈ J, w r ≤ min (r₀ : ℝ) (#(univ.filter fun r => w r = 0) : ℝ) := by
  classical
  -- Each nonzero weight is at most `-1/2`.
  have hle : ∀ r, w r ≠ 0 → w r ≤ -1 / 2 := by
    intro r hr
    obtain ⟨n, hn⟩ := hw_half r
    have h1 : (n : ℝ) ≤ 0 := by linarith [hw_nonpos r]
    have h2 : n ≠ 0 := by rintro rfl; simp [hn] at hr
    have h3 : n ≤ -1 := by
      have : n ≤ 0 := by exact_mod_cast h1
      omega
    have : (n : ℝ) ≤ -1 := by exact_mod_cast h3
    rw [hn]; linarith
  set Jz := J.filter fun r => w r = 0
  set Jn := J.filter fun r => ¬ w r = 0
  have hcard : #Jz + #Jn = k := by rw [card_filter_add_card_filter_not, hJ]
  have hsum : ∑ r ∈ J, w r = ∑ r ∈ Jz, w r + ∑ r ∈ Jn, w r :=
    (sum_filter_add_sum_filter_not J _ _).symm
  have hz : ∑ r ∈ Jz, w r = 0 := sum_eq_zero fun r hr => (mem_filter.1 hr).2
  have hn : ∑ r ∈ Jn, w r ≤ #Jn * (-1 / 2) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun r hr => hle r (mem_filter.1 hr).2
  have hmain : (k : ℝ) + 2 * ∑ r ∈ J, w r ≤ #Jz := by
    rw [hsum, hz, ← hcard]; push_cast; linarith
  have hJz_k : #Jz ≤ r₀ := by
    have := card_filter_le J fun r => w r = 0
    omega
  have hJz_z : #Jz ≤ #(univ.filter fun r => w r = 0) :=
    card_le_card (filter_subset_filter _ (subset_univ J))
  exact le_min (hmain.trans (by exact_mod_cast hJz_k)) (hmain.trans (by exact_mod_cast hJz_z))

end Zeta5Irr
