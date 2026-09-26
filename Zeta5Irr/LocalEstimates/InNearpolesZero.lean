/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.MA
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# Nonzero multiples of `p` of bounded size

For a prime `p` and an integer `A ≥ 0`, the nonzero integers `r` with `|r| ≤ A` and
`r ≡ 0 (mod p)` are exactly `r = k p` with `1 ≤ |k| ≤ ⌊A / p⌋ = m_A`, so there are `2 m_A` of
them.

## Main results

* `Zeta5Irr.card_filter_Icc_modEq_zero`: `#{r ∈ ℤ : 0 < |r| ≤ A, r ≡ 0 (mod p)} = 2 m_A`.

## Implementation notes

* The source takes `p` prime. The count holds for every natural number `p`: for `p = 0` both
  sides vanish, since `r ≡ 0 (mod 0)` forces `r = 0` and `m_A = A / 0 = 0`.
* The integers `r` with `|r| ≤ A` are enumerated as `Finset.Icc (-A) A ⊆ ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5: the inner range: the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- **Nonzero multiples of `p` in `[-A, A]`.** The number of integers `r` with `0 < |r| ≤ A`
and `r ≡ 0 (mod p)` is `2 m_A`. -/
@[zeta5irr "lem_in_nearpoles_zero"]
theorem card_filter_Icc_modEq_zero (p A : ℕ) :
    #{r ∈ Icc (-(A : ℤ)) A | 0 < |r| ∧ r ≡ 0 [ZMOD p]} = 2 * mA p A := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [mA, Nat.div_zero, mul_zero, card_eq_zero, filter_eq_empty_iff]
    intro r _ ⟨hr, h⟩
    simp only [Nat.cast_zero, Int.ModEq, Int.emod_zero] at h
    simp [h] at hr
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  set m := mA p A with hm
  have hmZ : (m : ℤ) = (A : ℤ) / p := by rw [hm, mA, Int.natCast_div]
  have key : {r ∈ Icc (-(A : ℤ)) A | 0 < |r| ∧ r ≡ 0 [ZMOD p]} =
      ((Icc (-(m : ℤ)) m).erase 0).map ⟨(· * (p : ℤ)), mul_left_injective₀ hp'.ne'⟩ := by
    ext r
    simp only [mem_filter, mem_Icc, mem_map, mem_erase, Function.Embedding.coeFn_mk,
      Int.modEq_zero_iff_dvd]
    simp only [hmZ, neg_le (a := (A : ℤ) / p), Int.le_ediv_iff_mul_le hp']
    constructor
    · rintro ⟨⟨h₁, h₂⟩, hr, k, rfl⟩
      exact ⟨k, ⟨fun hk => by simp [hk] at hr, by linarith, by linarith⟩, mul_comm _ _⟩
    · rintro ⟨k, ⟨hk, h₁, h₂⟩, rfl⟩
      exact ⟨⟨by linarith, by linarith⟩, abs_pos.2 (mul_ne_zero hk hp'.ne'), k, mul_comm _ _⟩
  rw [key, card_map, card_erase_of_mem (by simp), Int.card_Icc]
  omega

end Zeta5Irr
