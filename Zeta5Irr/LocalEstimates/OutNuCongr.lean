/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleValue
public import Zeta5Irr.LocalEstimates.OutHarmCongr
public import Mathlib.Tactic.ENatToNat

/-!
# The two pole values at a split class are congruent

Let `p` be an odd prime and `1 ≤ a < p`. Then `ν_a(X) - ν_{p-a}(X) ∈ p ℤ_p[X]`, where
`ν_j(X) = j ^ 4 (X - H_j^{(5)}) - 1/4 + 1/(2j)` is the pole value.

The coefficient of `X` in the difference is the integer `a ^ 4 - (p - a) ^ 4`, which is divisible
by `p` since `p - a ≡ -a` and `(-a) ^ 4 = a ^ 4`. The constant coefficient is
`-a ^ 4 H_a^{(5)} + (p - a) ^ 4 H_{p-a}^{(5)} + 1/(2a) - 1/(2(p - a))`, a `p`-adic integer whose
reduction modulo `p` is computed in `𝔽_p`: there `p - a = -a`,
`H_{p-a}^{(5)} ≡ H_{a-1}^{(5)}` by the reflection congruence, and
`H_a^{(5)} - H_{a-1}^{(5)} = a⁻⁵`, so the reduction is `-a ^ 4 a⁻⁵ + 1/(2a) + 1/(2a) = 0`.

## Main results

* `Zeta5Irr.norm_coeff_poleValue_sub_poleValue_lt_one`: every coefficient of
  `ν_a - ν_{p-a}` lies in `p ℤ_p`.

## Implementation notes

* Membership of a rational number in `p ℤ_p` is stated as `‖x‖ < 1` for its image in `ℚ_p`,
  as in the reflection congruence for `H^{(5)}`; so `ν_a - ν_{p-a} ∈ p ℤ_p[X]` is stated
  coefficientwise.
* The source assumes `p ≥ 7` and `1 ≤ a ≤ m° = (p - 1) / 2`. The congruence holds for every
  odd prime `p` and every `1 ≤ a < p`, and is stated in that generality. Oddness of `p` is the
  hypothesis `p ≠ 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.9 (The outer range: congruences at a split class).
-/

@[expose] public section

open Polynomial Finset

namespace Zeta5Irr

/-- **The two pole values at a split class are congruent.** For an odd prime `p` and
`1 ≤ a < p`, every coefficient of `ν_a(X) - ν_{p-a}(X)` lies in `p ℤ_p`, i.e. its image in
`ℚ_p` has norm less than one: `ν_a(X) - ν_{p-a}(X) ∈ p ℤ_p[X]`. -/
@[zeta5irr "lem_out_nu_congr"]
theorem norm_coeff_poleValue_sub_poleValue_lt_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ}
    (ha : 1 ≤ a) (hap : a < p) (n : ℕ) :
    ‖((poleValue a - poleValue (p - a)).coeff n : ℚ_[p])‖ < 1 := by
  have hpr : p.Prime := Fact.out
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · obtain ⟨x, hx, hx'⟩ := exists_padicInt_harmonicFive_toZMod (p := p) (m := a) hap
      obtain ⟨y, hy, hy'⟩ := exists_padicInt_harmonicFive_toZMod (p := p) (m := p - a)
        (by omega)
      have hcop : ∀ m, 0 < m → m < p → ‖((2 * m : ℕ) : ℤ_[p])‖ = 1 := fun m hm hmp =>
        PadicInt.norm_natCast_eq_one_iff.2 <| Nat.Coprime.mul_right
          ((Nat.coprime_primes hpr Nat.prime_two).2 hp)
          (Nat.coprime_of_lt_prime hm.ne' hmp hpr)
      have hu : IsUnit ((2 * a : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2 (hcop a ha hap)
      have hw : IsUnit ((2 * (p - a) : ℕ) : ℤ_[p]) :=
        PadicInt.isUnit_iff.2 (hcop (p - a) (by omega) (by omega))
      set z : ℤ_[p] := -((a : ℤ_[p]) ^ 4 * x) + ((p - a : ℕ) : ℤ_[p]) ^ 4 * y +
        ↑hu.unit⁻¹ - ↑hw.unit⁻¹ with hz
      have hzq : (z : ℚ_[p]) = ((poleValue a - poleValue (p - a)).coeff 0 : ℚ_[p]) := by
        rw [hz, PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_add, PadicInt.coe_neg,
          PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_pow, hx, hy]
        have e : ∀ {m : ℕ} (h : IsUnit (m : ℤ_[p])),
            ((h.unit⁻¹ : ℤ_[p]ˣ) : ℚ_[p]) = ((m : ℚ_[p]))⁻¹ := fun {m} h => by
          have h' := congrArg ((↑) : ℤ_[p] → ℚ_[p]) h.unit.inv_mul
          rw [PadicInt.coe_mul, PadicInt.coe_one] at h'
          rw [eq_inv_of_mul_eq_one_left h', h.unit_spec, PadicInt.coe_natCast]
        rw [e hu, e hw, PadicInt.coe_natCast, PadicInt.coe_natCast]
        rw [coeff_sub, coeff_zero_poleValue, coeff_zero_poleValue]
        push_cast
        ring
      have hmem : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        have e1 := map_units_inv (PadicInt.toZMod (p := p)) hu.unit
        have e2 := map_units_inv (PadicInt.toZMod (p := p)) hw.unit
        simp only [IsUnit.unit_spec, map_natCast] at e1 e2
        obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
        set b : ZMod p := ((k + 1 : ℕ) : ZMod p) with hbdef
        set s : ZMod p := ∑ v ∈ Icc 1 k, ((v : ZMod p) ^ 5)⁻¹ with hsdef
        have hSa : ∑ v ∈ Icc 1 (k + 1), ((v : ZMod p) ^ 5)⁻¹ = s + (b ^ 5)⁻¹ :=
          sum_Icc_succ_top (by omega) _
        have hSpa : ∑ v ∈ Icc 1 (p - (k + 1)), ((v : ZMod p) ^ 5)⁻¹ = s := by
          rw [sum_Icc_inv_pow_five_zmod hp ha hap.le, Nat.add_sub_cancel]
        have hpa : ((p - (k + 1) : ℕ) : ZMod p) = -b := by
          rw [Nat.cast_sub hap.le, ZMod.natCast_self, zero_sub]
          rfl
        have hval : PadicInt.toZMod z =
            -(b ^ 4 * (s + (b ^ 5)⁻¹)) + (-b) ^ 4 * s + (2 * b)⁻¹ - (2 * -b)⁻¹ := by
          rw [hz, RingHom.map_sub, RingHom.map_add, RingHom.map_add, RingHom.map_neg,
            RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, hx', hy', e1, e2,
            hSa, hSpa, map_natCast, map_natCast, Nat.cast_mul, Nat.cast_mul, hpa]
          rfl
        have hk : b ≠ 0 := by
          rw [hbdef, Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (by omega) hap
        have h2 : (2 : ZMod p) ≠ 0 := by
          have := (ZMod.natCast_eq_zero_iff 2 p).not.2
            (Nat.not_dvd_of_pos_of_lt two_pos (lt_of_le_of_ne hpr.two_le (Ne.symm hp)))
          exact_mod_cast this
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hval]
        field_simp
        ring
      rw [← hzq]
      exact PadicInt.mem_nonunits.1 hmem
    · rw [coeff_sub, coeff_one_poleValue, coeff_one_poleValue]
      have hint : ((a : ℚ) ^ 4 - ((p - a : ℕ) : ℚ) ^ 4) =
          (((a : ℤ) ^ 4 - ((p : ℤ) - a) ^ 4 : ℤ) : ℚ) := by
        push_cast [Nat.cast_sub hap.le]
        ring
      rw [hint, Rat.cast_intCast, Padic.norm_intCast_lt_one_iff]
      exact ⟨-(p : ℤ) ^ 3 + 4 * p ^ 2 * a - 6 * p * a ^ 2 + 4 * a ^ 3, by ring⟩
  · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_sub_le _ _).trans_lt
      (max_lt ((natDegree_poleValue_le _).trans_lt hn) ((natDegree_poleValue_le _).trans_lt hn)))]
    simp

end Zeta5Irr
