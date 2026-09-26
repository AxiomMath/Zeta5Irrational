/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.EllA
public import Zeta5Irr.LocalEstimates.MA

/-!
# The total of `ℓ_A` over the half-range

For an odd prime `p` and an integer `A ≥ 0`,
`∑_{a = 1}^{m°} ℓ_A(a) = A - m_A`.

The pairs `{a, p - a}` with `1 ≤ a ≤ m° = (p - 1) / 2` partition the nonzero residues modulo `p`,
so every `1 ≤ j ≤ A` with `p ∤ j` is counted by exactly one `ℓ_A(a)`, and there are `m_A`
multiples of `p` in `{1, …, A}`.

## Main results

* `Zeta5Irr.sum_ellA_mStar`: `∑_{a = 1}^{m°} ℓ_A(a) = A - m_A`.

## Implementation notes

* The source takes `p` an odd prime; the argument uses only that `p` is odd, so primality is
  dropped.
* The partition is realised by the map sending `j` to its residue `r = j mod p` if `r ≤ m°`
  and to `p - r` otherwise; `ℓ_A(a)`, which counts integers `1 ≤ j ≤ A`, is identified via
  `Int.toNat` with the fibre of this map over `a` inside `{j ∈ ℕ : 1 ≤ j ≤ A, p ∤ j}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3 (The inner range: dimensions).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For odd `p`, `∑_{a = 1}^{m°} ℓ_A(a) = A - m_A`: the integers `1 ≤ j ≤ A` prime to `p` are
each counted by exactly one `ℓ_A(a)` with `1 ≤ a ≤ m°`. -/
@[zeta5irr "lem_in_ell_total"]
theorem sum_ellA_mStar {p : ℕ} (hp : Odd p) (A : ℕ) :
    ∑ a ∈ Icc 1 (mStar p), ellA p A a = A - mA p A := by
  have h2 := two_mul_mStar_add_one hp
  set m := mStar p
  let f : ℕ → ℕ := fun j => if j % p ≤ m then j % p else p - j % p
  have hp0 : 0 < p := by omega
  have hfib : ∀ a ∈ Icc 1 m,
      ellA p A a = #{j ∈ ({j ∈ Icc 1 A | ¬p ∣ j} : Finset ℕ) | f j = a} := by
    intro a ha
    rw [mem_Icc] at ha
    have key : ∀ j : ℕ, ((j : ℤ) ≡ (a : ℕ) [ZMOD p] ∨ (j : ℤ) ≡ -((a : ℕ) : ℤ) [ZMOD p]) ↔
        (¬p ∣ j ∧ f j = a) := by
      intro j
      have hneg : -(a : ℤ) ≡ ((p - a : ℕ) : ℤ) [ZMOD p] := by
        rw [Nat.cast_sub (by omega)]
        exact Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
      have hr := Nat.mod_lt j hp0
      have e1 : (j : ℤ) ≡ (a : ℕ) [ZMOD p] ↔ j % p = a := by
        rw [Int.natCast_modEq_iff, Nat.ModEq, Nat.mod_eq_of_lt (a := a) (by omega)]
      have e2 : (j : ℤ) ≡ -((a : ℕ) : ℤ) [ZMOD p] ↔ j % p = p - a := by
        rw [← Nat.mod_eq_of_lt (a := p - a) (b := p) (by omega), ← Nat.ModEq,
          ← Int.natCast_modEq_iff]
        exact ⟨fun h => h.trans hneg, fun h => h.trans hneg.symm⟩
      rw [e1, e2, Nat.dvd_iff_mod_eq_zero]
      simp only [f]
      split_ifs <;> omega
    rw [ellA_eq_card_filter_nat, filter_filter]
    exact congrArg card (filter_congr fun j _ => by
      rw [natCast_eq_or_eq_neg_iff_intModEq, key])
  have hmaps : Set.MapsTo f (({j ∈ Icc 1 A | ¬p ∣ j} : Finset ℕ) : Set ℕ) (Icc 1 m) := by
    intro j hj
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Icc, Nat.dvd_iff_mod_eq_zero] at hj
    have hr := Nat.mod_lt j hp0
    simp only [f, coe_Icc, Set.mem_Icc]
    split_ifs <;> omega
  rw [sum_congr rfl hfib, ← card_eq_sum_card_fiberwise hmaps, filter_not, card_sdiff_of_subset
    (filter_subset _ _), show Icc 1 A = Ioc 0 A from rfl, Nat.Ioc_filter_dvd_card_eq_div]
  simp

end Zeta5Irr
