/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Kappa
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.ENatToNat

/-!
# The `p`-adic valuation of the weights `κ_d`

For a prime `p ≥ 5` the weights `κ_d = d (d - 1) (d - 2) B_{d-3} / 24` satisfy
`v_p(κ_d) ≥ -1` for every `d`. The factor `d (d - 1) (d - 2)` is an integer and `24 = 2^3 · 3`
is a `p`-adic unit, so this reduces to `v_p(B_m) ≥ -1`, which holds for every prime `p` and
every `m`: `B_0 = 1`, `B_1 = -1/2`, `B_m = 0` for odd `m ≥ 3`, and for even `m = 2k > 0` the
theorem of von Staudt–Clausen gives `v_p(B_{2k}) = -1` if `(p - 1) ∣ 2k` and
`v_p(B_{2k}) ≥ 0` otherwise.

## Main results

* `Zeta5Irr.norm_bernoulli_two_mul_le_one`: `B_{2k} ∈ ℤ_p` when `(p - 1) ∤ 2k`, from the
  von Staudt–Clausen decomposition `Zeta5Irr.exists_bernoulli_two_mul_eq`.
* `Zeta5Irr.neg_one_le_padicValRat_bernoulli`: `-1 ≤ v_p(B_n)` for every prime `p` and `n : ℕ`;
  in norm form `Zeta5Irr.norm_bernoulli_le`: `|B_n|_p ≤ p`.
* `Zeta5Irr.norm_twentyFour_eq_one`: `‖24‖_p = 1` for `p ≥ 5`.
* `Zeta5Irr.neg_one_le_padicValRat_kappa`: `-1 ≤ v_p(κ_d)` for all primes `p ≥ 5` and all `d`.

## Implementation notes

The valuation is Mathlib's `padicValRat`, which assigns `0` rather than `+∞` to `0`; since
`0 ≥ -1`, the bound `-1 ≤ padicValRat p (kappa d)` is equivalent to the statement
`v_p(κ_d) ≥ -1` with the convention `v_p(0) = +∞`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The von Staudt–Clausen decomposition, cast to `ℚ_[p]`: `B_{2k} = n - ∑ 1 / q` for an
integer `n`, the sum over the primes `q` with `(q - 1) ∣ 2k`. -/
theorem exists_bernoulli_two_mul_eq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ∃ n : ℤ, (bernoulli (2 * k) : ℚ_[p]) =
      n - ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 / q : ℚ_[p]) := by
  obtain ⟨n, hn⟩ := Bernoulli.vonStaudt_clausen k
  refine ⟨n, ?_⟩
  have : bernoulli (2 * k) =
      n - ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 / q : ℚ) := by
    rw [hn]; ring
  rw [this]
  push_cast
  rfl

/-- If `(p - 1) ∤ 2k`, the Bernoulli number `B_{2k}` is a `p`-adic integer. -/
theorem norm_bernoulli_two_mul_le_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    (hk : ¬ (p - 1) ∣ 2 * k) : ‖(bernoulli (2 * k) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_bernoulli_two_mul_eq p k
  rw [hn, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (Padic.norm_int_le_one n) ?_)
  rw [norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q hq => ?_
  obtain ⟨-, hq, hqk⟩ := by simpa using hq
  have hqp : q ≠ p := by rintro rfl; exact hk hqk
  have hcop : p.Coprime q := (Nat.coprime_primes hp.out hq).2 hqp.symm
  simp [norm_inv, Padic.norm_natCast_eq_one_iff.2 hcop]

/-- For a prime `p ≥ 5`, `24 = 2^3 · 3` is a `p`-adic unit: `‖24‖_p = 1`. -/
theorem norm_twentyFour_eq_one {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ‖(24 : ℚ_[p])‖ = 1 := by
  have : p.Coprime (2 ^ 3 * 3) :=
    ((Nat.coprime_primes hp.out Nat.prime_two).2 (by omega)).pow_right 3 |>.mul_right
      ((Nat.coprime_primes hp.out Nat.prime_three).2 (by omega))
  exact_mod_cast Padic.norm_natCast_eq_one_iff.2 this

/-- A rational number `q` with `v_p(q) ≥ -1` satisfies `‖q‖_p ≤ p`. -/
theorem norm_ratCast_le_of_neg_one_le_padicValRat {p : ℕ} [hp : Fact p.Prime] {q : ℚ}
    (h : -1 ≤ padicValRat p q) : ‖(q : ℚ_[p])‖ ≤ p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [Padic.eq_padicNorm]
  by_cases h0 : q = 0
  · simp [h0]
  rw [padicNorm.eq_zpow_of_nonzero h0]
  push_cast
  calc (p : ℝ) ^ (-padicValRat p q) ≤ (p : ℝ) ^ (1 : ℤ) := zpow_le_zpow_right₀ hp1.le (by omega)
    _ = p := zpow_one _

/-- For every prime `p` and every `n`, the Bernoulli number `B_n` satisfies `v_p(B_n) ≥ -1`. -/
theorem neg_one_le_padicValRat_bernoulli (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    -1 ≤ padicValRat p (bernoulli n) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    by_cases hpk : p - 1 ∣ 2 * k
    · exact (Bernoulli.padicValRat_bernoulli hk hpk).ge
    · have h := (Padic.norm_le_one_iff_val_nonneg _).1
        (norm_bernoulli_two_mul_le_one (p := p) hpk)
      rw [Padic.valuation_ratCast] at h
      linarith
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [bernoulli_one, neg_div, padicValRat.neg, padicValRat.div one_ne_zero two_ne_zero,
        padicValRat.one, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
      have : padicValNat p 2 ≤ 1 := by
        by_cases h2 : p = 2
        · subst h2; simp
        · rw [padicValNat.eq_zero_of_not_dvd fun h =>
            h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h)]
          simp
      omega
    · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one k) (by omega)]
      simp

/-- For every prime `p` and every `n`, `|B_n|_p ≤ p`. -/
theorem norm_bernoulli_le {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ‖((_root_.bernoulli n : ℚ) : ℚ_[p])‖ ≤ p :=
  norm_ratCast_le_of_neg_one_le_padicValRat (neg_one_le_padicValRat_bernoulli p n)

/-- For a prime `p ≥ 5`, the weight `κ_d` satisfies `v_p(κ_d) ≥ -1` for every `d`. -/
@[zeta5irr "lem_kappa_val"]
theorem neg_one_le_padicValRat_kappa {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (d : ℕ) :
    -1 ≤ padicValRat p (kappa d) := by
  by_cases h0 : kappa d = 0
  · simp [h0]
  have hc : (d.descFactorial 3 : ℚ) ≠ 0 := by
    intro h; apply h0; rw [kappa, h]; simp
  have hB : bernoulli (d - 3) ≠ 0 := by
    intro h; apply h0; rw [kappa, h]; simp
  have h24 : padicValRat p (24 : ℚ) = 0 := by
    rw [show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    rw [padicValNat.eq_zero_of_not_dvd]
    · simp
    intro h
    have : p ∣ 2 ^ 3 * 3 := h
    rcases (Nat.Prime.dvd_mul hp.out).1 this with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega
  rw [kappa, padicValRat.div (mul_ne_zero hc hB) (by norm_num), padicValRat.mul hc hB, h24,
    padicValRat.of_nat]
  have := neg_one_le_padicValRat_bernoulli p (d - 3)
  have : (0 : ℤ) ≤ padicValNat p (d.descFactorial 3) := by positivity
  linarith

end Zeta5Irr
