/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InE

/-!
# The range of the number of extras `E`

For an odd prime `p` and an integer `M ≥ 40`, the number of extras
`E = h - L₀ + 3 (N - m_N) - m° T` satisfies `0 ≤ E < m°`. Indeed `T = ⌊S / m°⌋` with
`S = h - L₀ + 3 (N - m_N)`, so `E = S - m° T` is the remainder of `S` modulo `m° = (p - 1) / 2`,
and `m° ≥ 1` once `p ≥ 3`.

## Main results

* `Zeta5Irr.extraCount_nonneg`: `0 ≤ E`.
* `Zeta5Irr.extraCount_lt_mStar`: `E < m°`.

## Implementation notes

* The source assumes that `p` is an odd prime and `M ≥ 40`. Only `m° ≥ 1`, i.e. `p ≥ 3`, is used,
  so the lemmas assume `3 ≤ p` alone; an odd prime satisfies it. The bound `M ≥ 40` plays no role.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The number of extras is nonnegative: `0 ≤ E`, for `p ≥ 3`. -/
@[zeta5irr "lem_in_E_range"]
theorem extraCount_nonneg (n : ℕ) {p : ℕ} (M : ℕ) (hp : 3 ≤ p) : 0 ≤ extraCount n p M := by
  rw [extraCount_eq_emod]
  exact Int.emod_nonneg _ (by have := mStar_def p; omega)

/-- The number of extras is less than the number of nonzero square classes: `E < m°`,
for `p ≥ 3`. -/
@[zeta5irr "lem_in_E_range"]
theorem extraCount_lt_mStar (n : ℕ) {p : ℕ} (M : ℕ) (hp : 3 ≤ p) :
    extraCount n p M < mStar p := by
  rw [extraCount_eq_emod]
  exact Int.emod_lt_of_pos _ (by have := mStar_def p; omega)

end Zeta5Irr
