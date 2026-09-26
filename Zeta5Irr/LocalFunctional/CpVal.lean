/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Cp
public import Zeta5Irr.LocalFunctional.TauAnFar
public import Zeta5Irr.LocalFunctional.PowerSumNegFour

/-!
# The valuation of the constant `C_p`

For a prime `p ≥ 7`, the constant `C_p = ∑_{a=1}^{p-1} τ^an(ε_{-a/p})` lies in `p^5 ℤ_p`.

For `s = -a/p` one has `s⁻¹ = -p/a`, of norm `p⁻¹`, and
`τ^an(ε_s) = -(1/4) ∑_{k ≥ 0} binom(k+3, 3) B_k s^{-k-4}`. The term `k = 0` is
`-(1/4) p^4 a^{-4}`, and summed over `a` it lies in `p^5 ℤ_p` because
`∑_{a=1}^{p-1} a^{-4} ∈ p ℤ_p`. The term `k = 1` has norm `p^{-5}` since `B_1 = -1/2`, and
each term `k ≥ 2` has norm at most `p · p^{-k-4} ≤ p^{-5}` since `v_p(B_k) ≥ -1`.

## Main results

* `Zeta5Irr.norm_Cp_le`: for a prime `p ≥ 7`, `‖C_p‖ ≤ p^{-5}`, i.e. `C_p ∈ p^5 ℤ_p`.

## Implementation notes

Membership in `p^5 ℤ_p` is expressed as `‖C_p‖ ≤ (p^5)⁻¹`, which for an element of
`ℚ_[p]` is equivalent to it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- For `1 ≤ a ≤ p - 1`, the inverse `(-a/p)⁻¹ = -p/a` has norm `p⁻¹`. -/
theorem norm_inv_neg_natCast_div_prime {a : ℕ} (ha : a ∈ Ico 1 p) :
    ‖(-((a : ℚ_[p]) / p))⁻¹‖ = (p : ℝ)⁻¹ := by
  obtain ⟨h1, h2⟩ := mem_Ico.mp ha
  have hna : ‖(a : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 (Nat.coprime_of_lt_prime (by omega) h2 Fact.out)
  rw [norm_inv, norm_neg, norm_div, hna, Padic.norm_p]
  simp

/-- **`C_p ∈ p^5 ℤ_p`.** For a prime `p ≥ 7`, the constant
`C_p = ∑_{a=1}^{p-1} τ^an(ε_{-a/p})` has `p`-adic norm at most `p^{-5}`. -/
@[zeta5irr "lem_Cp_val"]
theorem norm_Cp_le (hp : 7 ≤ p) : ‖Cp p‖ ≤ ((p : ℝ) ^ 5)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpi0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hpi1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  -- `v_p(B_k) ≥ -1`, i.e. `‖B_k‖ ≤ p`
  have hBk : ∀ k : ℕ, ‖(bernoulli k : ℚ_[p])‖ ≤ p := norm_bernoulli_le
  have h2 : ‖(2 : ℚ_[p])‖ = 1 := by
    rw [show (2 : ℚ_[p]) = ((2 : ℤ) : ℚ_[p]) by norm_num, Padic.norm_intCast_eq_one_iff]
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes Nat.prime_two Fact.out).mpr (by omega))
  have h4 : ‖(1 / 4 : ℚ_[p])‖ = 1 := by
    rw [norm_div, show (4 : ℚ_[p]) = 2 * 2 by norm_num, norm_mul, h2]; simp
  set T : ℕ → ℕ → ℚ_[p] := fun a k => -(1 / 4) * (((k + 3).choose 3 : ℚ_[p]) *
    (bernoulli k : ℚ_[p]) * (-((a : ℚ_[p]) / p))⁻¹ ^ (k + 4)) with hT
  -- split each `τ^an(ε_{-a/p})` into the term `k = 0` and the rest
  have hsplit : ∀ a : ℕ, a ∈ Ico 1 p → tauAn (farEps (-((a : ℚ_[p]) / (p : ℚ_[p])))) =
      T a 0 + ∑' k : ℕ, T a (k + 1) := by
    intro a ha
    have h := hasSum_tauAn_farEps (by omega) (s := -((a : ℚ_[p]) / (p : ℚ_[p])))
      (by
        obtain ⟨h1, h2⟩ := mem_Ico.mp ha
        rw [show -((a : ℚ_[p]) / p) = ((-a : ℤ) : ℚ_[p]) / p by push_cast; ring,
          valuation_intCast_div_prime (by
            rw [dvd_neg, Int.natCast_dvd_natCast]
            exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))]
        norm_num)
    have h' := (hasSum_nat_add_iff' 1).mpr h
    rw [h'.tsum_eq]
    simp [T]
  have hCp : Cp p = ∑ a ∈ Ico 1 p, T a 0 + ∑ a ∈ Ico 1 p, ∑' k : ℕ, T a (k + 1) := by
    rw [Cp, ← sum_add_distrib]
    exact sum_congr rfl hsplit
  rw [hCp]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · -- the terms `k = 0`
    have hIco : Ico 1 p = Icc 1 (p - 1) := by
      ext a; simp only [mem_Ico, mem_Icc]; omega
    have hsum : ∑ a ∈ Ico 1 p, T a 0 =
        -(1 / 4) * (p : ℚ_[p]) ^ 4 * ∑ a ∈ Icc 1 (p - 1), ((a : ℚ_[p]) ^ 4)⁻¹ := by
      rw [hIco, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      simp only [T]
      have hp0' : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      simp only [zero_add, Nat.choose_self, Nat.cast_one, bernoulli_zero, Rat.cast_one, one_mul]
      rw [inv_neg, inv_div]
      ring
    rw [hsum, norm_mul, norm_mul, norm_neg, h4, Padic.norm_p_pow, one_mul]
    calc (p : ℝ) ^ (-(4 : ℕ) : ℤ) * ‖∑ a ∈ Icc 1 (p - 1), ((a : ℚ_[p]) ^ 4)⁻¹‖
        ≤ (p : ℝ) ^ (-(4 : ℕ) : ℤ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (norm_sum_inv_pow_four_le p hp) (by positivity)
      _ = ((p : ℝ) ^ 5)⁻¹ := by
          rw [zpow_neg, zpow_natCast]; field_simp
  · -- the terms `k ≥ 1`
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun a ha => ?_
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    simp only [T]
    rw [norm_mul, norm_neg, h4, one_mul, norm_mul, norm_mul, norm_pow,
      norm_inv_neg_natCast_div_prime ha]
    have hC : ‖(((k + 1 + 3).choose 3 : ℕ) : ℚ_[p])‖ ≤ 1 := by
      simpa using Padic.norm_int_le_one (p := p) (((k + 1 + 3).choose 3 : ℕ) : ℤ)
    have hB : ‖(bernoulli (k + 1) : ℚ_[p])‖ * (p : ℝ)⁻¹ ^ (k + 1 + 4) ≤
        ((p : ℝ) ^ 5)⁻¹ := by
      rcases k with _ | k
      · rw [bernoulli_one]
        push_cast
        rw [neg_div, norm_neg, norm_div, norm_one, h2]
        simp [inv_pow]
      · calc ‖(bernoulli (k + 1 + 1) : ℚ_[p])‖ * (p : ℝ)⁻¹ ^ (k + 1 + 1 + 4)
            ≤ p * (p : ℝ)⁻¹ ^ (k + 1 + 1 + 4) :=
              mul_le_mul_of_nonneg_right (hBk _) (by positivity)
          _ = (p : ℝ)⁻¹ ^ 5 * (p : ℝ)⁻¹ ^ k := by
              rw [show k + 1 + 1 + 4 = 1 + (5 + k) by ring, pow_add, pow_add, pow_one,
                ← mul_assoc, mul_inv_cancel₀ hp0.ne', one_mul]
          _ ≤ (p : ℝ)⁻¹ ^ 5 * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ hpi0 hpi1) (by positivity)
          _ = ((p : ℝ) ^ 5)⁻¹ := by rw [mul_one, inv_pow]
    calc ‖(((k + 1 + 3).choose 3 : ℕ) : ℚ_[p])‖ * ‖(bernoulli (k + 1) : ℚ_[p])‖ *
          (p : ℝ)⁻¹ ^ (k + 1 + 4)
        ≤ 1 * ‖(bernoulli (k + 1) : ℚ_[p])‖ * (p : ℝ)⁻¹ ^ (k + 1 + 4) := by gcongr
      _ ≤ ((p : ℝ) ^ 5)⁻¹ := by rw [one_mul]; exact hB

end Zeta5Irr
