/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InEps
public import Zeta5Irr.LocalEstimates.InERange

/-!
# The number of extras handed out

For an odd prime `p` and an integer `M ≥ 40`, the extras indicators `ε_a` of the square classes
`1 ≤ a ≤ m°` sum to the number of extras: `∑_{a=1}^{m°} ε_a = E`. Indeed the sum counts the
indices `a` with `rk(a) < E`; since `rk` is a bijection from `{1, …, m°}` onto `{0, …, m° - 1}`,
this count is `min(E, m°)`, which is `E` because `0 ≤ E < m°`.

## Main results

* `Zeta5Irr.sum_extraIndicator_eq_extraCount`: `∑_{1 ≤ a ≤ m°} ε_a = E`.

## Implementation notes

* The source assumes that `p` is an odd prime and `M ≥ 40`. Only `p ≥ 3` is used (it gives
  `0 ≤ E < m°`), so the lemma assumes `3 ≤ p` alone; an odd prime satisfies it.
* The sum is a natural number and `E` an integer, so the identity is stated in `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `p ≥ 3`, exactly `E` of the square classes `1 ≤ a ≤ m°` receive an extra:
`∑_{1 ≤ a ≤ m°} ε_a = E`. -/
@[zeta5irr "lem_in_eps_count"]
theorem sum_extraIndicator_eq_extraCount (n : ℕ) {p : ℕ} (M : ℕ) (hp : 3 ≤ p) :
    ((∑ a ∈ Icc 1 (mStar p), extraIndicator n p M a : ℕ) : ℤ) = extraCount n p M :=
  sum_extraIndicator (extraCount_nonneg n M hp) (extraCount_lt_mStar n M hp).le

end Zeta5Irr
