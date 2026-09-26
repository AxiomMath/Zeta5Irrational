/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutTp

/-!
# The counting identity behind `t_p`

Let `p` be an odd prime with `2N < p`, and let `v_K = K mod p`. The source shows that the
small-class partial count `t_p = min(N, v_K) + u` counts the small classes `1 ≤ a ≤ N` with
`a ≤ v_K`, together with those with `p - a ≤ v_K`:
`#{1 ≤ a ≤ N : a ≤ v_K} + #{1 ≤ a ≤ N : p - a ≤ v_K} = t_p`.

The first set is `{1, …, min(N, v_K)}`. Since `p - a ≤ v_K` is equivalent to `a ≥ p - v_K`,
the second set is `{p - v_K, …, N}`, of size `max(0, N + v_K - p + 1) = u`.

## Main results

* `Zeta5Irr.filter_le_vA_eq_Icc`: the first set is `{1, …, min(N, v_K)}`.
* `Zeta5Irr.filter_sub_le_vA_eq_Icc`: the second set is `{p - v_K, …, N}`.
* `Zeta5Irr.card_filter_le_vA_add_card_filter_sub_le_vA`: the counting identity
  `#{1 ≤ a ≤ N : a ≤ v_K} + #{1 ≤ a ≤ N : p - a ≤ v_K} = t_p`.

## Implementation notes

* The source assumes `p` is an odd prime with `2N < p`. The identity only needs `p > 0`
  (so that `v_K < p`), and is stated under that hypothesis. The subtraction `p - a` is
  truncated natural subtraction; `p - a ≤ v_K ↔ p ≤ v_K + a` holds for all `a`, so no
  condition `a ≤ p` is needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11: the outer range, the counting behind (4.14).
-/

@[expose] public section

namespace Zeta5Irr

/-- The small classes `1 ≤ a ≤ N` with `a ≤ v_K` are exactly `{1, …, min(N, v_K)}`. -/
theorem filter_le_vA_eq_Icc (p N K : ℕ) :
    (Finset.Icc 1 N).filter (· ≤ vA p K) = Finset.Icc 1 (min N (vA p K)) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The small classes `1 ≤ a ≤ N` with `p - a ≤ v_K` are exactly `{p - v_K, …, N}`,
provided `p > 0`. -/
theorem filter_sub_le_vA_eq_Icc {p : ℕ} (hp : 0 < p) (N K : ℕ) :
    (Finset.Icc 1 N).filter (fun a => p - a ≤ vA p K) = Finset.Icc (p - vA p K) N := by
  have := vA_lt hp K
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The counting behind (4.14): for `p > 0` (in the source, an odd prime with `2N < p`),
`#{1 ≤ a ≤ N : a ≤ v_K} + #{1 ≤ a ≤ N : p - a ≤ v_K} = t_p`. -/
@[zeta5irr "lem_out_tp_count"]
theorem card_filter_le_vA_add_card_filter_sub_le_vA {p : ℕ} (hp : 0 < p) (N K : ℕ) :
    ((Finset.Icc 1 N).filter (· ≤ vA p K)).card +
        ((Finset.Icc 1 N).filter (fun a => p - a ≤ vA p K)).card =
      smallClassCount p N K := by
  have := vA_lt hp K
  rw [filter_le_vA_eq_Icc, filter_sub_le_vA_eq_Icc hp, Nat.card_Icc, Nat.card_Icc,
    smallClassCount, overlapCount]
  omega

end Zeta5Irr
