/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.EllA
public import Zeta5Irr.LocalEstimates.InVA
public import Mathlib.Data.Int.CardIntervalMod

/-!
# A closed formula for `ℓ_A(a)`

Let `p` be an odd prime, `A ≥ 0` and `1 ≤ a ≤ m° = (p - 1) / 2`. Write `A = p m_A + v_A` with
`0 ≤ v_A < p`. Then
`ℓ_A(a) = 2 m_A + 𝟙[a ≤ v_A] + 𝟙[p - a ≤ v_A]`.

Indeed, the residues `a` and `-a ≡ p - a` are distinct and nonzero modulo `p`, so `ℓ_A(a)` is
the sum of the numbers of `1 ≤ j ≤ A` congruent to `a` and to `p - a`. For a residue
`1 ≤ c ≤ p`, the number of `1 ≤ j ≤ A` with `j ≡ c` is `m_A + 𝟙[c ≤ v_A]`: each of the `m_A`
complete blocks `{kp + 1, …, kp + p}` contributes one, and the final partial block
`{p m_A + 1, …, p m_A + v_A}` contributes one exactly when `c ≤ v_A`.

## Main results

* `Zeta5Irr.card_filter_Icc_natModEq`: for `1 ≤ c ≤ p`, the number of `1 ≤ j ≤ A` with
  `j ≡ c (mod p)` is `m_A + 𝟙[c ≤ v_A]`.
* `Zeta5Irr.ellA_eq_two_mul_mA_add`: `ℓ_A(a) = 2 m_A + 𝟙[a ≤ v_A] + 𝟙[p - a ≤ v_A]` for
  `1 ≤ a ≤ m°`.

## Implementation notes

* The source assumes `p` is an odd prime. Neither primality nor oddness is used: the hypothesis
  `1 ≤ a ≤ m° = (p - 1) / 2` alone gives `1 ≤ a` and `2a < p`, which is all the argument needs,
  so the formula is stated for an arbitrary natural number `p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For a residue `1 ≤ c ≤ p`, the number of `1 ≤ j ≤ A` with `j ≡ c (mod p)` is
`m_A + 𝟙[c ≤ v_A]`. -/
theorem card_filter_Icc_natModEq {p c : ℕ} (hc : 1 ≤ c) (hcp : c ≤ p) (A : ℕ) :
    #{j ∈ Icc 1 A | j ≡ c [MOD p]} = mA p A + if c ≤ vA p A then 1 else 0 := by
  have hp : 0 < p := by omega
  have key : #{j ∈ Icc 1 A | j ≡ c [MOD p]} = #{j ∈ range A | j ≡ c - 1 [MOD p]} := by
    refine card_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [coe_filter, mem_Icc, mem_range, Set.mem_ofPred_eq] at hj ⊢
      refine ⟨by omega, Nat.ModEq.add_right_cancel' 1 ?_⟩
      rw [Nat.sub_add_cancel hj.1.1, Nat.sub_add_cancel hc]
      exact hj.2
    · intro j hj
      simp only [coe_filter, mem_Icc, mem_range, Set.mem_ofPred_eq] at hj ⊢
      refine ⟨by omega, ?_⟩
      have := hj.2.add_right 1
      rwa [Nat.sub_add_cancel hc] at this
    · intro j hj
      simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hj
      simp only
      omega
    · intro j _
      simp
  rw [key, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hp,
    Nat.mod_eq_of_lt (by omega : c - 1 < p)]
  simp only [vA]
  congr 1
  split_ifs <;> omega

/-- **The formula for `ℓ_A(a)`.** For `1 ≤ a ≤ m° = (p - 1) / 2`,
`ℓ_A(a) = 2 m_A + 𝟙[a ≤ v_A] + 𝟙[p - a ≤ v_A]`. -/
@[zeta5irr "lem_in_ell_formula"]
theorem ellA_eq_two_mul_mA_add {p a : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) (A : ℕ) :
    ellA p A a = 2 * mA p A + (if a ≤ vA p A then 1 else 0) +
      (if p - a ≤ vA p A then 1 else 0) := by
  have h2a : 2 * a < p := by rw [mStar_def] at ham; omega
  have hneg : -(a : ℤ) ≡ ((p - a : ℕ) : ℤ) [ZMOD p] := by
    rw [Int.modEq_iff_dvd, Nat.cast_sub (by omega)]
    exact ⟨1, by ring⟩
  have hsplit : ellA p A a =
      #{j ∈ Icc 1 A | j ≡ a [MOD p]} + #{j ∈ Icc 1 A | j ≡ p - a [MOD p]} := by
    rw [← card_union_of_disjoint, ← filter_or]
    · rw [ellA_eq_card_filter_nat]
      refine congrArg card (filter_congr fun j _ => ?_)
      rw [natCast_eq_or_eq_neg_iff_intModEq, ← Int.natCast_modEq_iff, ← Int.natCast_modEq_iff]
      exact or_congr Iff.rfl ⟨fun h => h.trans hneg, fun h => h.trans hneg.symm⟩
    · refine disjoint_filter.2 fun j _ h₁ h₂ => ?_
      have := h₁.symm.trans h₂
      have := this.eq_of_lt_of_lt (by omega) (by omega)
      omega
  rw [hsplit, card_filter_Icc_natModEq ha (by omega),
    card_filter_Icc_natModEq (by omega) (by omega)]
  ring

end Zeta5Irr
