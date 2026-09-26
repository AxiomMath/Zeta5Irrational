/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleValue
public import Zeta5Irr.LocalFunctional.HarmonicFivePadicInt
public import Mathlib.Tactic.ENatToNat

/-!
# The pole values have `p`-integral coefficients

Let `p` be an odd prime and `j < p`. The pole value
`ν_j(X) = j ^ 4 (X - H_j^{(5)}) - 1/4 + 1/(2j)` has coefficients in `ℤ_p`: the coefficient of
`X` is the integer `j ^ 4`, and in the constant coefficient `H_j^{(5)} ∈ ℤ_p` because every
denominator `v ≤ j < p` is a unit, `4` is a unit because `p` is odd, and `2j` is a unit because
`p` is odd and `j < p`.

## Main results

* `Zeta5Irr.norm_coeff_poleValue_le_one`: every coefficient of `ν_j` has `p`-adic norm at most
  one.
* `Zeta5Irr.poleValue_mem_lifts_padicInt`: `ν_j`, viewed in `ℚ_p[X]`, lies in `ℤ_p[X]`.

## Implementation notes

* Membership of `ν_j` in `ℤ_p[X]` is stated as `ν_j ∈ Polynomial.lifts (ℤ_p → ℚ_p)` for the
  image of `ν_j` in `ℚ_p[X]`: `ν_j` is the image of a polynomial with coefficients in `ℤ_p`.
* The source assumes `1 ≤ j < p`. The case `j = 0` also holds, since Lean's convention
  `1 / 0 = 0` gives `ν_0 = -1/4`, so only `j < p` is assumed. Oddness of `p` is the hypothesis
  `p ≠ 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.9: the outer range, congruences at a split class.
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- For an odd prime `p` and `j < p`, every coefficient of the pole value `ν_j` lies in `ℤ_p`:
its `p`-adic norm is at most one. -/
theorem norm_coeff_poleValue_le_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {j : ℕ} (hj : j < p)
    (n : ℕ) : ‖((poleValue j).coeff n : ℚ_[p])‖ ≤ 1 := by
  have hpr : p.Prime := Fact.out
  have h2 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 <| (Nat.coprime_primes hpr Nat.prime_two).2 hp
  have hjn : ‖(j : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) j
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have hH := norm_harmonicFive_le_one (p := p) hj
      have h4 : ‖(1 / 4 : ℚ_[p])‖ = 1 := by
        have : (4 : ℚ_[p]) = ((2 : ℕ) : ℚ_[p]) ^ 2 := by norm_num
        rw [this, norm_div, norm_pow, h2, norm_one]
        norm_num
      have h2j : ‖(1 / (2 * (j : ℚ_[p])))‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp
        have hjn' : ‖(j : ℚ_[p])‖ = 1 :=
          Padic.norm_natCast_eq_one_iff.2 (Nat.coprime_of_lt_prime hj0.ne' hj hpr)
        have h2' : ‖(2 : ℚ_[p])‖ = 1 := by exact_mod_cast h2
        rw [norm_div, norm_mul, h2', hjn']
        simp
      rw [coeff_zero_poleValue]
      push_cast
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ h2j)
      rw [sub_eq_add_neg]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (by rw [norm_neg, h4]))
      rw [norm_neg, norm_mul, norm_pow]
      exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hjn) hH (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    · rw [coeff_one_poleValue]
      push_cast
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hjn
  · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_poleValue_le j).trans_lt hn)]
    simp

/-- **The pole values are `p`-integral.** For an odd prime `p` and `j < p`, the pole value
`ν_j(X)`, viewed in `ℚ_p[X]`, lies in `ℤ_p[X]`. -/
@[zeta5irr "lem_out_nu_int"]
theorem poleValue_mem_lifts_padicInt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {j : ℕ} (hj : j < p) :
    (poleValue j).map (Rat.castHom ℚ_[p]) ∈ lifts (PadicInt.Coe.ringHom (p := p)) := by
  rw [lifts_iff_coeff_lifts]
  intro n
  rw [coeff_map]
  exact ⟨⟨_, norm_coeff_poleValue_le_one hp hj n⟩, rfl⟩

end Zeta5Irr
