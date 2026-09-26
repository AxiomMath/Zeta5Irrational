/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsOut

/-!
# Counting the vanishing entry valuations of the outer range

Let `ℓ = ℓ_K(a)` and suppose `δ_a = 1`. The entry valuations `w_{a,i}` for `0 ≤ i ≤ ℓ - 2`
are `min(0, i + 1 - ℓ / 2)` for `i < ℓ - 2` and `0` for `i = ℓ - 2`, so `w_{a,i}` vanishes
exactly when `ℓ ≤ 2 i + 2`. The indices with this property form the interval
`[⌈ℓ / 2⌉ - 1, ℓ - 2]`, which has `⌊ℓ / 2⌋` elements.

## Main results

* `Zeta5Irr.card_filter_outerWeight_eq_zero`: for `δ_a = 1`,
  `#{0 ≤ i ≤ ℓ_K(a) - 2 : w_{a,i} = 0} = ⌊ℓ_K(a) / 2⌋`.

## Implementation notes

* The source assumes `p` prime, `1 ≤ a ≤ m°` and `2 ≤ ℓ_K(a) ≤ 6`, and checks the count case
  by case. The count equals `⌊ℓ_K(a) / 2⌋` for every value of `ℓ_K(a)`, so the result is
  stated with the single hypothesis `δ_a = 1`. For `ℓ_K(a) ≤ 1` the index range
  `0 ≤ i ≤ ℓ_K(a) - 2` is empty and both sides vanish.
* The index range `0 ≤ i ≤ ℓ_K(a) - 2` is `Finset.range (ℓ_K(a) - 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11: the outer range, the counting behind (4.14).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- **The zero count in the outer range.** For `δ_a = 1`, exactly `⌊ℓ_K(a) / 2⌋` of the
entry valuations `w_{a,i}`, `0 ≤ i ≤ ℓ_K(a) - 2`, vanish. -/
@[zeta5irr "lem_out_zerocount_removed"]
theorem card_filter_outerWeight_eq_zero {p K : ℕ} {N a : ℤ} (hδ : outerDelta N a = 1) :
    #{i ∈ range (ellA p K a - 1) | outerWeight p K N a i = 0} = ellA p K a / 2 := by
  have : {i ∈ range (ellA p K a - 1) | outerWeight p K N a i = 0} =
      Ico ((ellA p K a - 1) / 2) (ellA p K a - 1) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico, outerWeight_eq_zero_iff, hδ]
    omega
  rw [this, Nat.card_Ico]
  omega

end Zeta5Irr
