/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar

/-!
# The two small members of a residue class pair

Let `p` be an odd prime with `p ≤ K < 3p` and let `1 ≤ a ≤ m° = (p - 1) / 2`. The source
observes that the indices `1 ≤ j ≤ K` with `j ≡ ±a (mod p)` and `j < p` are exactly `a` and
`p - a`: these are the unique representatives in `{1, …, p - 1}` of the residues `a` and `-a`,
and they are distinct since `a ≤ m° < p - a`.

## Main results

* `Zeta5Irr.filter_Icc_lt_class_eq`: the set
  `{j : 1 ≤ j ≤ K, j < p, j ≡ ±a (mod p)}` equals `{a, p - a}`.
* `Zeta5Irr.card_filter_Icc_lt_class`: this set has exactly two elements.

## Implementation notes

* The congruence `j ≡ ±a (mod p)` is stated in `ZMod p`, as
  `(j : ZMod p) = a ∨ (j : ZMod p) = -a`, as for the residue-class polynomial `Ξ_a`.
* The source assumes `p` is an odd prime and `K < 3p`. Neither primality, oddness, nor the
  upper bound on `K` is needed: `1 ≤ a ≤ (p - 1) / 2` already forces `2a < p`, and only
  `p ≤ K` is used.
* The index `j` and the residue `a` are natural numbers.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8 (The outer range: the separating basis).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `p ≤ K` and `1 ≤ a ≤ m°`, the indices `1 ≤ j ≤ K` with `j < p` and `j ≡ ±a (mod p)`
are exactly `a` and `p - a`. -/
@[zeta5irr "lem_out_class_split"]
theorem filter_Icc_lt_class_eq {p K a : ℕ} (hpK : p ≤ K) (ha : 1 ≤ a) (ham : a ≤ mStar p) :
    (Icc 1 K).filter (fun j : ℕ ↦ j < p ∧ ((j : ZMod p) = a ∨ (j : ZMod p) = -a)) =
      {a, p - a} := by
  rw [mStar_def] at ham
  have h2a : 2 * a < p := by omega
  ext j
  simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
  have hneg : (j : ZMod p) = -a ↔ p ∣ j + a := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  rw [hneg, ZMod.natCast_eq_natCast_iff']
  constructor
  · rintro ⟨⟨hj1, -⟩, hjp, h | ⟨c, hc⟩⟩
    · left
      rwa [Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt (by omega)] at h
    · right
      rcases c with _ | _ | c <;> grind
  · rintro (rfl | rfl)
    · exact ⟨⟨ha, by omega⟩, by omega, Or.inl rfl⟩
    · exact ⟨⟨by omega, by omega⟩, by omega, Or.inr ⟨1, by omega⟩⟩

/-- For `p ≤ K` and `1 ≤ a ≤ m°`, exactly two indices `1 ≤ j ≤ K` satisfy `j < p` and
`j ≡ ±a (mod p)`. -/
theorem card_filter_Icc_lt_class {p K a : ℕ} (hpK : p ≤ K) (ha : 1 ≤ a) (ham : a ≤ mStar p) :
    #((Icc 1 K).filter (fun j : ℕ ↦ j < p ∧ ((j : ZMod p) = a ∨ (j : ZMod p) = -a))) = 2 := by
  rw [filter_Icc_lt_class_eq hpK ha ham, card_pair]
  rw [mStar_def] at ham
  omega

end Zeta5Irr
