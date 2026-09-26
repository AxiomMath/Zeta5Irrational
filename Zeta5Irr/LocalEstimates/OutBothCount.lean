/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutVGeN
public import Zeta5Irr.LocalEstimates.OutTpCount

/-!
# The small classes hit twice

Let `p` be an odd prime with `2N < p`, let `v_K = K mod p`, and let
`u = max(0, N + v_K - p + 1)` be the overlap count. Then `u` counts the small classes
`1 ≤ a ≤ N` hit twice, that is those with both `a ≤ v_K` and `p - a ≤ v_K`:
`#{1 ≤ a ≤ N : a ≤ v_K ∧ p - a ≤ v_K} = u`.

If `u = 0` then `N + v_K < p`, so no `a ≤ N` satisfies `p - a ≤ v_K` and the set is empty.
If `u > 0` then `v_K ≥ N`, so the condition `a ≤ v_K` is automatic and the set is
`{1 ≤ a ≤ N : p - a ≤ v_K} = {p - v_K, …, N}`, of size `u`.

## Main results

* `Zeta5Irr.filter_le_vA_and_sub_le_vA_eq_Icc`: for `2N < p` the set is `{p - v_K, …, N}`.
* `Zeta5Irr.card_filter_le_vA_and_sub_le_vA`: for `2N < p`,
  `#{1 ≤ a ≤ N : a ≤ v_K ∧ p - a ≤ v_K} = u`.

## Implementation notes

* The source assumes `p` is an odd prime; the argument is pure arithmetic and uses only
  `2N < p`, so `p`, `N` and `K` are arbitrary natural numbers here. The subtraction `p - a`
  is truncated natural subtraction, which agrees with the integer one since `a ≤ N < p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `2N < p`, the small classes `1 ≤ a ≤ N` with both `a ≤ v_K` and `p - a ≤ v_K` are
exactly `{p - v_K, …, N}`. -/
theorem filter_le_vA_and_sub_le_vA_eq_Icc {p N : ℕ} (hNp : 2 * N < p) (K : ℕ) :
    (Finset.Icc 1 N).filter (fun a => a ≤ vA p K ∧ p - a ≤ vA p K) =
      Finset.Icc (p - vA p K) N := by
  rcases Nat.eq_zero_or_pos (overlapCount p N K) with hu | hu
  · rw [overlapCount_eq_zero_iff] at hu
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · have := le_vA_of_overlapCount_pos hNp hu
    rw [← filter_sub_le_vA_eq_Icc (by omega) N K]
    refine Finset.filter_congr fun a ha => ?_
    rw [Finset.mem_Icc] at ha
    exact and_iff_right (ha.2.trans this)

/-- The counting behind (4.14): for `2N < p` (in the source, an odd prime),
`#{1 ≤ a ≤ N : a ≤ v_K ∧ p - a ≤ v_K} = u`. -/
@[zeta5irr "lem_out_both_count"]
theorem card_filter_le_vA_and_sub_le_vA {p N : ℕ} (hNp : 2 * N < p) (K : ℕ) :
    ((Finset.Icc 1 N).filter (fun a => a ≤ vA p K ∧ p - a ≤ vA p K)).card =
      overlapCount p N K := by
  have := vA_lt (show 0 < p by omega) K
  rw [filter_le_vA_and_sub_le_vA_eq_Icc hNp, Nat.card_Icc, overlapCount]
  omega

end Zeta5Irr
