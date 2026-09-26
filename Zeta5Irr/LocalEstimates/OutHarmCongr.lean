/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.RingHoms
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# A reflection congruence for the harmonic sums of order five

Let `p` be an odd prime and `1 ≤ a ≤ p`. Then `H_{p-a}^{(5)} - H_{a-1}^{(5)} ∈ p ℤ_p`.

Both harmonic sums lie in `ℤ_p`, since their denominators are prime to `p`, so it suffices to
compare their images in the residue field `ℤ_p / p ℤ_p = 𝔽_p`. There the full sum
`∑_{v=1}^{p-1} v⁻⁵` equals `∑_{x ∈ 𝔽_p} x⁵`, after the substitution `x = v⁻¹`, which vanishes;
and the substitution `v = p - w` turns the tail `∑_{v=p-a+1}^{p-1} v⁻⁵` into
`-∑_{w=1}^{a-1} w⁻⁵`.

## Main results

* `Zeta5Irr.exists_padicInt_harmonicFive_toZMod`: for `m < p`, `H_m^{(5)}` is the image of a
  `p`-adic integer whose residue modulo `p` is `∑_{v=1}^{m} v⁻⁵ ∈ 𝔽_p`.
* `Zeta5Irr.sum_Icc_inv_pow_five_reflect`: in a field of characteristic `p`,
  `∑_{v=1}^{p-1} v⁻⁵ = ∑_{v=1}^{p-a} v⁻⁵ - ∑_{w=1}^{a-1} w⁻⁵`.
* `Zeta5Irr.sum_Icc_inv_pow_five_zmod_eq_zero`: `∑_{v=1}^{p-1} v⁻⁵ = 0` in `𝔽_p`, `p` odd.
* `Zeta5Irr.sum_Icc_inv_pow_five_zmod`: in `𝔽_p` with `p` odd, the reflection identity
  `∑_{v=1}^{p-a} v⁻⁵ = ∑_{v=1}^{a-1} v⁻⁵` for `1 ≤ a ≤ p`.
* `Zeta5Irr.norm_harmonicFive_sub_harmonicFive_lt_one`: the congruence
  `H_{p-a}^{(5)} - H_{a-1}^{(5)} ∈ p ℤ_p`.

## Implementation notes

* Membership of a rational number in `p ℤ_p` is stated as `‖x‖ < 1` for its image in `ℚ_p`;
  since the `p`-adic norm takes values in `p ^ ℤ`, this is the same as `‖x‖ ≤ p⁻¹`.
* The source assumes `p ≥ 7` and `1 ≤ a ≤ m° = (p - 1) / 2`. The congruence holds for every
  odd prime `p` and every `1 ≤ a ≤ p`, and is stated in that generality: the vanishing of
  `∑_{x ∈ 𝔽_p} x⁵` follows from `5 < p - 1` when `p ≥ 7`, and for `p = 3, 5` from
  `x⁵ = x` in `𝔽_p` and `1 < p - 1`. Oddness of `p` is the hypothesis `p ≠ 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.9 (The outer range: congruences at a split class).
-/

@[expose] public section

open Finset

namespace Zeta5Irr

/-- For a prime `p` and `m < p`, the harmonic sum `H_m^{(5)}` is the image of a `p`-adic
integer whose reduction modulo `p` is `∑_{v=1}^{m} v⁻⁵` computed in `ZMod p`. -/
theorem exists_padicInt_harmonicFive_toZMod {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m < p) :
    ∃ z : ℤ_[p], (z : ℚ_[p]) = harmonicFive m ∧
      PadicInt.toZMod z = ∑ v ∈ Icc 1 m, ((v : ZMod p) ^ 5)⁻¹ := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨z, hz, hz'⟩ := ih (by omega)
    have hu : IsUnit (((m + 1 : ℕ) : ℤ_[p]) ^ 5) :=
      (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
        (Nat.coprime_of_lt_prime (by omega) hm Fact.out))).pow 5
    refine ⟨z + ↑hu.unit⁻¹, ?_, ?_⟩
    · have h := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hu.unit.inv_mul
      rw [PadicInt.coe_mul, PadicInt.coe_one] at h
      rw [PadicInt.coe_add, hz, harmonicFive_succ, eq_inv_of_mul_eq_one_left h, hu.unit_spec]
      push_cast
      rfl
    · rw [map_add, map_units_inv, hz', IsUnit.unit_spec, sum_Icc_succ_top (by omega)]
      simp

/-- In a field of characteristic `p`, the substitution `v = p - w` gives
`∑_{v=1}^{p-1} v⁻⁵ = ∑_{v=1}^{p-a} v⁻⁵ - ∑_{w=1}^{a-1} w⁻⁵` for `1 ≤ a ≤ p`. -/
theorem sum_Icc_inv_pow_five_reflect {K : Type*} [Field K] (p : ℕ) [CharP K p] {a : ℕ}
    (ha : 1 ≤ a) (hap : a ≤ p) :
    ∑ v ∈ Icc 1 (p - 1), ((v : K) ^ 5)⁻¹ =
      ∑ v ∈ Icc 1 (p - a), ((v : K) ^ 5)⁻¹ - ∑ v ∈ Icc 1 (a - 1), ((v : K) ^ 5)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega) (by omega), sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hsplit : p - (k + 1) = (p - (k + 1 + 1)) + 1 := by omega
    rw [hsplit, sum_Icc_succ_top (by omega : 1 ≤ p - (k + 1 + 1) + 1)]
    have hcast : (((p - (k + 1 + 1) + 1 : ℕ)) : K) = -((k + 1 : ℕ) : K) := by
      rw [← hsplit, Nat.cast_sub (by omega), CharP.cast_eq_zero]
      ring
    rw [hcast, (by decide : Odd 5).neg_pow, inv_neg]
    ring

/-- In `ZMod p` with `p` an odd prime, `∑_{v=1}^{p-1} v⁻⁵ = 0`. -/
theorem sum_Icc_inv_pow_five_zmod_eq_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∑ v ∈ Icc 1 (p - 1), ((v : ZMod p) ^ 5)⁻¹ = 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrange : ∑ v ∈ range p, ((v : ZMod p) ^ 5)⁻¹ = ∑ x : ZMod p, (x ^ 5)⁻¹ := by
    refine sum_nbij (fun v : ℕ => (v : ZMod p)) (by simp) ?_ ?_ (by simp)
    · intro a ha b hb h
      simpa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (mem_range.1 ha),
        Nat.mod_eq_of_lt (mem_range.1 hb)] using h
    · intro x _
      exact ⟨x.val, by simpa using ZMod.val_lt x, by simp⟩
  have hinv : ∑ x : ZMod p, (x ^ 5)⁻¹ = ∑ x : ZMod p, x ^ 5 := by
    simp_rw [← inv_pow]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ fun _ => rfl
  have hpow : ∑ x : ZMod p, x ^ 5 = 0 := by
    have hpr : p.Prime := Fact.out
    rcases hpr.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hp
    rcases (show k = 1 ∨ k = 2 ∨ k = 0 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · -- `p = 3`: `x ^ 5 = x ^ 3 * x ^ 2 = x ^ 3 = x`
      subst hk
      have h : ∀ x : ZMod 3, x ^ 5 = x ^ 1 := fun x => by
        rw [show 5 = 3 + 2 by rfl, pow_add, ZMod.pow_card, ← pow_succ', ZMod.pow_card, pow_one]
      simp_rw [h]
      exact FiniteField.sum_pow_lt_card_sub_one _ _ (by rw [ZMod.card]; omega)
    · -- `p = 5`: `x ^ 5 = x`
      subst hk
      have h : ∀ x : ZMod 5, x ^ 5 = x ^ 1 := fun x =>
        (ZMod.pow_card x).trans (pow_one x).symm
      simp_rw [h]
      exact FiniteField.sum_pow_lt_card_sub_one _ _ (by rw [ZMod.card]; omega)
    · exact absurd hpr (by rw [hk]; norm_num)
    · exact FiniteField.sum_pow_lt_card_sub_one _ _ (by rw [ZMod.card]; omega)
  have hIcc : Icc 1 (p - 1) = Ico 1 p := by ext; simp; omega
  have hsplit := sum_eq_sum_Ico_succ_bot (show 0 < p by omega)
    (fun v : ℕ => ((v : ZMod p) ^ 5)⁻¹)
  rw [← range_eq_Ico, hrange, hinv, hpow] at hsplit
  rw [Nat.cast_zero, zero_pow (by norm_num), inv_zero, zero_add] at hsplit
  rw [hIcc]
  exact hsplit.symm

/-- **Reflection of `∑ v⁻⁵` modulo `p`.** In `ZMod p` with `p` an odd prime and `1 ≤ a ≤ p`,
`∑_{v=1}^{p-a} v⁻⁵ = ∑_{v=1}^{a-1} v⁻⁵`. -/
theorem sum_Icc_inv_pow_five_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ} (ha : 1 ≤ a)
    (hap : a ≤ p) :
    ∑ v ∈ Icc 1 (p - a), ((v : ZMod p) ^ 5)⁻¹ = ∑ v ∈ Icc 1 (a - 1), ((v : ZMod p) ^ 5)⁻¹ :=
  (sub_eq_zero.1 ((sum_Icc_inv_pow_five_reflect p ha hap).symm.trans
    (sum_Icc_inv_pow_five_zmod_eq_zero hp)))

/-- **Congruence for the harmonic sums of order five.** For an odd prime `p` and `1 ≤ a ≤ p`,
`H_{p-a}^{(5)} - H_{a-1}^{(5)} ∈ p ℤ_p`, i.e. its image in `ℚ_p` has norm less than one. -/
@[zeta5irr "lem_out_harm_congr"]
theorem norm_harmonicFive_sub_harmonicFive_lt_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ}
    (ha : 1 ≤ a) (hap : a ≤ p) :
    ‖((harmonicFive (p - a) - harmonicFive (a - 1) : ℚ) : ℚ_[p])‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := exists_padicInt_harmonicFive_toZMod (p := p) (m := p - a) (by omega)
  obtain ⟨y, hy, hy'⟩ := exists_padicInt_harmonicFive_toZMod (p := p) (m := a - 1) (by omega)
  have hmem : x - y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hx', hy',
      sum_Icc_inv_pow_five_zmod hp ha hap]
    exact sub_self _
  have hlt : ‖x - y‖ < 1 := PadicInt.mem_nonunits.1 hmem
  rw [Rat.cast_sub, ← hx, ← hy, ← PadicInt.coe_sub]
  exact hlt

end Zeta5Irr
