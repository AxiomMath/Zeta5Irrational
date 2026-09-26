/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsOut

/-!
# The cost of a column with `δ_a = 0` in the outer range

Let `p` be a prime and `1 ≤ a ≤ m°` with `δ_a = 0` and `2 ≤ ℓ_K(a) ≤ 6`. Then the entry
valuations `w_{a,i}` of the outer range satisfy
`-2 ∑_{i=0}^{ℓ_K(a)-1} w_{a,i} = 7 (ℓ_K(a) - 2)`.

Indeed, with `δ_a = 0` the weight vanishes for `ℓ_K(a) - 2 ≤ i`, and for `i ≤ ℓ_K(a) - 3` the
bound `ℓ_K(a) ≤ 6` forces `i - (ℓ_K(a) + 4) / 2 < 0`, so `w_{a,i} = i - (ℓ_K(a) + 4) / 2`;
summing this arithmetic progression gives `(ℓ_K(a) - 2)(ℓ_K(a) + 4) - (ℓ_K(a) - 3)(ℓ_K(a) - 2)`.

## Main results

* `Zeta5Irr.neg_two_mul_sum_outerWeight_of_outerDelta_eq_zero`: the displayed identity.

## Implementation notes

* The source's hypotheses that `p` is prime and `1 ≤ a ≤ m°` are not used by the identity,
  so they are omitted; only `δ_a = 0` and `2 ≤ ℓ_K(a) ≤ 6` are assumed.
* The sum runs over `Finset.range (ℓ_K(a))`, that is `0 ≤ i ≤ ℓ_K(a) - 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- If `δ_a = 0` and `2 ≤ ℓ_K(a) ≤ 6`, then `-2 ∑_{i < ℓ_K(a)} w_{a,i} = 7 (ℓ_K(a) - 2)`. -/
@[zeta5irr "lem_out_cost_unremoved"]
theorem neg_two_mul_sum_outerWeight_of_outerDelta_eq_zero {p K : ℕ} {N a : ℤ}
    (hδ : outerDelta N a = 0) (h₂ : 2 ≤ ellA p K a) (h₆ : ellA p K a ≤ 6) :
    -2 * ∑ i ∈ range (ellA p K a), outerWeight p K N a i = 7 * ((ellA p K a : ℚ) - 2) := by
  simp only [outerWeight, hδ, Nat.cast_zero, mul_zero, add_zero]
  generalize ellA p K a = ℓ at h₂ h₆ ⊢
  interval_cases ℓ <;> simp [sum_range_succ] <;> norm_num

end Zeta5Irr
