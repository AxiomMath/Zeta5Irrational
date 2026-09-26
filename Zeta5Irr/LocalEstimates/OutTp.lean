/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutU

/-!
# The small-class partial count `t_p`

For a prime `p`, the source sets `t_p = min(N, v_K) + u`, where `v_K = K mod p` and
`u = max(0, N + v_K - p + 1)` is the overlap count. When `2N < p`, `t_p` counts the small
classes `1 ≤ a ≤ N` with `a ≤ v_K` together with those with `p - a ≤ v_K`, each class
counted once for every condition it satisfies.

## Main definitions

* `Zeta5Irr.smallClassCount`: the small-class partial count `t_p = min(N, v_K) + u`.

## Main results

* `Zeta5Irr.natCast_smallClassCount`: `(t_p : ℤ) = min N v_K + u`, read in `ℤ`.
* `Zeta5Irr.overlapCount_le_smallClassCount`: `u ≤ t_p`.
* `Zeta5Irr.min_le_smallClassCount`: `min(N, v_K) ≤ t_p`.
* `Zeta5Irr.smallClassCount_le`: `t_p ≤ 2N` for `p > 0`.

## Implementation notes

* The source takes `p` prime; primality is not needed to define `t_p`, so `p` is an arbitrary
  natural number here, as are `N` and `K` (the source fixes `N = 3n`, `K = 40n`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11: the outer range, the counting behind (4.14).
-/

@[expose] public section

namespace Zeta5Irr

/-- The small-class partial count `t_p = min(N, v_K) + u`, where `v_K = K mod p` and `u` is
the overlap count `Zeta5Irr.overlapCount`. -/
@[zeta5irr "def_out_tp"]
def smallClassCount (p N K : ℕ) : ℕ :=
  min N (vA p K) + overlapCount p N K

/-- The defining formula `t_p = min(N, v_K) + u`. -/
theorem smallClassCount_def (p N K : ℕ) :
    smallClassCount p N K = min N (vA p K) + overlapCount p N K :=
  rfl

/-- The defining formula `t_p = min(N, v_K) + u`, read in `ℤ`. -/
theorem natCast_smallClassCount (p N K : ℕ) :
    (smallClassCount p N K : ℤ) = min (N : ℤ) (vA p K) + overlapCount p N K := by
  simp [smallClassCount]

/-- The overlap count is at most the small-class partial count: `u ≤ t_p`. -/
theorem overlapCount_le_smallClassCount (p N K : ℕ) :
    overlapCount p N K ≤ smallClassCount p N K :=
  Nat.le_add_left _ _

/-- `min(N, v_K) ≤ t_p`. -/
theorem min_le_smallClassCount (p N K : ℕ) : min N (vA p K) ≤ smallClassCount p N K :=
  Nat.le_add_right _ _

/-- For `p > 0` the small-class partial count is at most `2N`. -/
theorem smallClassCount_le {p N : ℕ} (hp : 0 < p) (K : ℕ) : smallClassCount p N K ≤ 2 * N := by
  have := overlapCount_le (N := N) (K := K) hp
  unfold smallClassCount
  omega

end Zeta5Irr
