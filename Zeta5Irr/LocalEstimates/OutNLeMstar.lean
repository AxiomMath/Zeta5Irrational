/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar

/-!
# The inner degree is at most `m°`

If `p` is an odd prime with `2 N < p`, then `N ≤ m° = (p - 1) / 2`: since `2 N` and `p` are
integers, `2 N < p` gives `2 N ≤ p - 1`, and halving gives the claim.

## Main results

* `Zeta5Irr.le_mStar_of_two_mul_lt`: if `2 * N < p` then `N ≤ m°`.
* `Zeta5Irr.le_mStar_iff`: for `0 < p`, `N ≤ m°` if and only if `2 * N < p`.
* `Zeta5Irr.filter_Icc_one_mStar_le_eq`: if `2 * N < p`, `{1 ≤ a ≤ m° | a ≤ N} = {1, …, N}`.

## Implementation notes

* The source states the lemma for an odd prime `p` and the inner degree `N = 3 n`. Neither
  primality, oddness, nor the particular value of `N` is used, so `le_mStar_of_two_mul_lt` is
  stated for arbitrary natural numbers `N` and `p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8 (The outer range: the separating basis).
-/

@[expose] public section

namespace Zeta5Irr

/-- If `2 * N < p` then `N ≤ m° = (p - 1) / 2`. The source states this for an odd prime `p`
and the inner degree `N`; the inequality holds for all natural numbers. -/
@[zeta5irr "lem_out_N_le_mstar"]
theorem le_mStar_of_two_mul_lt {N p : ℕ} (h : 2 * N < p) : N ≤ mStar p := by
  rw [mStar_def]
  omega

/-- For `0 < p`, `N ≤ m°` if and only if `2 * N < p`. -/
theorem le_mStar_iff {N p : ℕ} (hp : 0 < p) : N ≤ mStar p ↔ 2 * N < p := by
  rw [mStar_def]
  omega

/-- If `2 * N < p`, the classes `1 ≤ a ≤ m°` with `a ≤ N` are `1 ≤ a ≤ N`. -/
theorem filter_Icc_one_mStar_le_eq {N p : ℕ} (h : 2 * N < p) :
    {a ∈ Finset.Icc 1 (mStar p) | a ≤ N} = Finset.Icc 1 N := by
  have := le_mStar_of_two_mul_lt h
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

end Zeta5Irr
