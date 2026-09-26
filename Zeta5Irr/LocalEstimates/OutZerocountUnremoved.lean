/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsOut

/-!
# The zero count of a column with `δ_a = 0` in the outer range

Let `p` be a prime and `1 ≤ a ≤ m°` with `δ_a = 0` and `2 ≤ ℓ_K(a) ≤ 6`. Then exactly two of
the entry valuations `w_{a,i}`, `0 ≤ i ≤ ℓ_K(a) - 1`, vanish.

Indeed, with `δ_a = 0` the weight `w_{a,i}` vanishes exactly when `ℓ_K(a) - 2 ≤ i` or
`ℓ_K(a) + 4 ≤ 2 i`. The first condition picks out the two indices `ℓ_K(a) - 2` and
`ℓ_K(a) - 1`; the second, for `i < ℓ_K(a) - 2`, would force `ℓ_K(a) ≥ 10`.

## Main results

* `Zeta5Irr.card_filter_outerWeight_eq_zero_of_outerDelta_eq_zero`: for `δ_a = 0` and
  `2 ≤ ℓ_K(a) ≤ 9`, `#{0 ≤ i ≤ ℓ_K(a) - 1 : w_{a,i} = 0} = 2`.

## Implementation notes

* The source's hypotheses that `p` is prime and `1 ≤ a ≤ m°` are not used by the count, so
  they are omitted.
* The source assumes `ℓ_K(a) ≤ 6`; the argument only needs `ℓ_K(a) ≤ 9`, which is what is
  assumed here. (For `ℓ_K(a) = 10` the index `i = 7` also has weight `0`.)
* The range `0 ≤ i ≤ ℓ_K(a) - 1` is `Finset.range (ℓ_K(a))`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- **The zero count of an unremoved column in the outer range.** For `δ_a = 0` and
`2 ≤ ℓ_K(a) ≤ 9`, exactly two of the entry valuations `w_{a,i}`, `0 ≤ i ≤ ℓ_K(a) - 1`,
vanish. -/
@[zeta5irr "lem_out_zerocount_unremoved"]
theorem card_filter_outerWeight_eq_zero_of_outerDelta_eq_zero {p K : ℕ} {N a : ℤ}
    (hδ : outerDelta N a = 0) (h₂ : 2 ≤ ellA p K a) (h₉ : ellA p K a ≤ 9) :
    #{i ∈ range (ellA p K a) | outerWeight p K N a i = 0} = 2 := by
  have : {i ∈ range (ellA p K a) | outerWeight p K N a i = 0} =
      Ico (ellA p K a - 2) (ellA p K a) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico,
      outerWeight_eq_zero_iff, hδ]
    omega
  rw [this, Nat.card_Ico]
  omega

end Zeta5Irr
