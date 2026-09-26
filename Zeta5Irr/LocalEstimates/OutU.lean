/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InVA

/-!
# The overlap count `u`

For a prime `p`, the source sets `u = max(0, N + v_K - p + 1)`, where `v_K = K mod p` is the
residue of `K` modulo `p`. When `2N < p`, `u` counts the small classes `1 ≤ a ≤ N` that are hit
twice, i.e. those with both `a ≤ v_K` and `p - a ≤ v_K`.

## Main definitions

* `Zeta5Irr.overlapCount`: the overlap count `u = max(0, N + v_K - p + 1)`.

## Main results

* `Zeta5Irr.natCast_overlapCount`: `(u : ℤ) = max 0 (N + v_K - p + 1)`, the source's formula.
* `Zeta5Irr.overlapCount_pos_iff`: `0 < u ↔ p ≤ N + v_K`.
* `Zeta5Irr.overlapCount_eq_zero_iff`: `u = 0 ↔ N + v_K < p`.

## Implementation notes

* `u` is defined with truncated natural subtraction, `N + v_K + 1 - p`, which realizes the
  `max 0 (·)` of the source exactly; `Zeta5Irr.natCast_overlapCount` recovers the integer formula.
* The source takes `p` prime; primality is not needed to define `u`, so `p` is an arbitrary
  natural number here, as are `N` and `K` (the source fixes `N = 3n`, `K = 40n`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11: the outer range, the counting behind (4.14).
-/

@[expose] public section

namespace Zeta5Irr

/-- The overlap count `u = max(0, N + v_K - p + 1)`, where `v_K = K mod p`. -/
@[zeta5irr "def_out_u"]
def overlapCount (p N K : ℕ) : ℕ :=
  N + vA p K + 1 - p

/-- The defining formula with truncated subtraction. -/
theorem overlapCount_def (p N K : ℕ) : overlapCount p N K = N + vA p K + 1 - p :=
  rfl

/-- The source's formula `u = max(0, N + v_K - p + 1)`, read in `ℤ`. -/
theorem natCast_overlapCount (p N K : ℕ) :
    (overlapCount p N K : ℤ) = max 0 ((N : ℤ) + vA p K - p + 1) := by
  unfold overlapCount
  omega

/-- The overlap count is positive exactly when `p ≤ N + v_K`. -/
theorem overlapCount_pos_iff {p N K : ℕ} : 0 < overlapCount p N K ↔ p ≤ N + vA p K := by
  unfold overlapCount
  omega

/-- The overlap count vanishes exactly when `N + v_K < p`. -/
theorem overlapCount_eq_zero_iff {p N K : ℕ} : overlapCount p N K = 0 ↔ N + vA p K < p := by
  unfold overlapCount
  omega

/-- When the overlap count is positive the subtraction does not truncate:
`u + p = N + v_K + 1`. -/
theorem overlapCount_add_of_pos {p N K : ℕ} (h : 0 < overlapCount p N K) :
    overlapCount p N K + p = N + vA p K + 1 := by
  unfold overlapCount at *
  omega

/-- A positive overlap count forces `p - N ≤ v_K`. -/
theorem sub_le_vA_of_overlapCount_pos {p N K : ℕ} (h : 0 < overlapCount p N K) :
    p - N ≤ vA p K := by
  rw [overlapCount_pos_iff] at h
  omega

/-- For `p > 0` the overlap count is at most `N`, since `v_K < p`. -/
theorem overlapCount_le {p N K : ℕ} (hp : 0 < p) : overlapCount p N K ≤ N := by
  have := vA_lt hp K
  unfold overlapCount
  omega

end Zeta5Irr
