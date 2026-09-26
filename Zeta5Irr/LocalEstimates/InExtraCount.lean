/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.InVA

/-!
# Counting the residues `a` and `p - a` below `v_A`

Let `p` be an odd prime, `m° = (p - 1) / 2` and `v_A` the least non-negative residue of `A`
modulo `p`. Each nonzero residue class modulo `p` has exactly one representative among
`a` and `p - a` for `1 ≤ a ≤ m°`. Consequently
`#{1 ≤ a ≤ m° : a ≤ v_A} + #{1 ≤ a ≤ m° : p - a ≤ v_A} = v_A`.

## Main results

* `Zeta5Irr.card_le_add_card_sub_le`: for odd `p` and `v < p`,
  `#{1 ≤ a ≤ m° : a ≤ v} + #{1 ≤ a ≤ m° : p - a ≤ v} = v`.
* `Zeta5Irr.card_le_vA_add_card_sub_le_vA`: the source's statement, with `v = v_A`.

## Implementation notes

* The identity holds for every `v < p` and every odd `p`; primality of `p` is not used.
  The subtraction `p - a` is truncated natural subtraction, which agrees with the integer
  one since `a ≤ m° < p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For odd `p` and `v < p`, the numbers `1 ≤ a ≤ m°` with `a ≤ v`, together with those with
`p - a ≤ v`, number exactly `v`. -/
theorem card_le_add_card_sub_le {p v : ℕ} (hp : Odd p) (hv : v < p) :
    #{a ∈ Icc 1 (mStar p) | a ≤ v} + #{a ∈ Icc 1 (mStar p) | p - a ≤ v} = v := by
  have h2 := two_mul_mStar_add_one hp
  have e1 : ({a ∈ Icc 1 (mStar p) | a ≤ v} : Finset ℕ) = Icc 1 (min (mStar p) v) := by
    ext a; simp only [mem_filter, mem_Icc, le_min_iff]; omega
  have e2 : ({a ∈ Icc 1 (mStar p) | p - a ≤ v} : Finset ℕ) = Icc (p - v) (mStar p) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [e1, e2, Nat.card_Icc, Nat.card_Icc]
  omega

/-- **Source form.** For an odd prime `p` and `A ≥ 0`,
`#{1 ≤ a ≤ m° : a ≤ v_A} + #{1 ≤ a ≤ m° : p - a ≤ v_A} = v_A`. -/
@[zeta5irr "lem_in_extra_count"]
theorem card_le_vA_add_card_sub_le_vA {p : ℕ} (hp : Odd p) (A : ℕ) :
    #{a ∈ Icc 1 (mStar p) | a ≤ vA p A} + #{a ∈ Icc 1 (mStar p) | p - a ≤ vA p A} =
      vA p A :=
  card_le_add_card_sub_le hp (vA_lt hp.pos A)

end Zeta5Irr
