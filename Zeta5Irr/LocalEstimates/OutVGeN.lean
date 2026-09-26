/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutU

/-!
# A positive overlap count forces `v_K ≥ N`

Let `p` be a prime with `2N < p`, and let `u = max(0, N + v_K - p + 1)` be the overlap count,
where `v_K = K mod p`. If `u > 0` then `N + v_K - p + 1 ≥ 1`, that is `v_K ≥ p - N`, and since
`2N < p` gives `p - N > N`, we get `v_K > N`; in particular `v_K ≥ N`.

## Main results

* `Zeta5Irr.lt_vA_of_overlapCount_pos`: if `2N < p` and `u > 0` then `N < v_K`.
* `Zeta5Irr.le_vA_of_overlapCount_pos`: if `2N < p` and `u > 0` then `N ≤ v_K`.

## Implementation notes

* The source assumes `p` is an odd prime; the argument is pure arithmetic and needs neither
  primality nor oddness, so `p`, `N` and `K` are arbitrary natural numbers here.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

/-- If `2N < p` and the overlap count `u` is positive, then `N < v_K`. -/
theorem lt_vA_of_overlapCount_pos {p N K : ℕ} (hNp : 2 * N < p)
    (hu : 0 < overlapCount p N K) : N < vA p K := by
  have := sub_le_vA_of_overlapCount_pos hu
  omega

/-- If `2N < p` and the overlap count `u` is positive, then `v_K ≥ N`. -/
@[zeta5irr "lem_out_v_ge_N"]
theorem le_vA_of_overlapCount_pos {p N K : ℕ} (hNp : 2 * N < p)
    (hu : 0 < overlapCount p N K) : N ≤ vA p K :=
  (lt_vA_of_overlapCount_pos hNp hu).le

end Zeta5Irr
