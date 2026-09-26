/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsOut
public import Mathlib.Tactic.Polynomial.Basic

/-!
# The cost of a removed class in the outer range

Let `ℓ = ℓ_K(a)` and suppose `δ_a = 1` and `2 ≤ ℓ ≤ 6`. Then the entry valuations of the
outer range satisfy
`-2 ∑_{i=0}^{ℓ-2} w_{a,i} = ⌊ℓ² / 4⌋ - ⌊ℓ / 2⌋`.

With `δ_a = 1` the weight vanishes at `i = ℓ - 2` and equals `min(0, i + 1 - ℓ/2)` for
`i < ℓ - 2`, so `-2 ∑ w_{a,i} = ∑_{i=0}^{ℓ-3} max(0, ℓ - 2 - 2i)`; both sides take the values
`0, 1, 2, 4, 6` at `ℓ = 2, …, 6`.

## Main results

* `Zeta5Irr.neg_two_mul_sum_outerWeight`: the displayed identity.

## Implementation notes

* The source assumes `p` prime and `1 ≤ a ≤ m°`; neither is used, so the lemma holds for
  arbitrary `p`, `K`, `N` and `a`, with only `δ_a = 1` and `2 ≤ ℓ_K(a) ≤ 6` assumed.
* The floors `⌊ℓ² / 4⌋` and `⌊ℓ / 2⌋` of nonnegative rationals are written as natural-number
  divisions `ℓ ^ 2 / 4` and `ℓ / 2`, cast to `ℚ`.
* The sum over `0 ≤ i ≤ ℓ - 2` is `∑ i ∈ Finset.range (ℓ - 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- If `δ_a = 1` and `2 ≤ ℓ_K(a) ≤ 6`, then
`-2 ∑_{i=0}^{ℓ_K(a)-2} w_{a,i} = ⌊ℓ_K(a)² / 4⌋ - ⌊ℓ_K(a) / 2⌋`. -/
@[zeta5irr "lem_out_cost_removed"]
theorem neg_two_mul_sum_outerWeight {p K : ℕ} {N a : ℤ} (hδ : outerDelta N a = 1)
    (h₂ : 2 ≤ ellA p K a) (h₆ : ellA p K a ≤ 6) :
    -2 * ∑ i ∈ range (ellA p K a - 1), outerWeight p K N a i =
      ((ellA p K a ^ 2 / 4 : ℕ) : ℚ) - ((ellA p K a / 2 : ℕ) : ℚ) := by
  simp only [outerWeight, hδ]
  generalize ellA p K a = ℓ at h₂ h₆ ⊢
  interval_cases ℓ <;> simp [sum_range_succ] <;> norm_num

end Zeta5Irr
