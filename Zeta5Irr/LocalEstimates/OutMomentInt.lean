/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MomentFunctional
public import Zeta5Irr.LocalFunctional.KappaVal
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.ENatToNat

/-!
# The moments `μ(t ^ e)` are `p`-adic integers for `e < 2p - 3`

Let `p ≥ 7` be a prime and `0 ≤ e < 2p - 3`. The moment
`μ(t ^ e) = (-1) ^ e B_{2e+2} (2e + 3)(2e + 4)(2e + 5) / 24` lies in `ℤ_p`.

By the theorem of von Staudt–Clausen, `B_{2k}` differs from an integer by the sum of `1 / q`
over the primes `q` with `(q - 1) ∣ 2k`. Hence `B_{2k} ∈ ℤ_p` when `(p - 1) ∤ 2k`, and in all
cases `p B_{2k} ∈ ℤ_p`. If `(p - 1) ∣ 2e + 2`, then `2e + 2 = k (p - 1)` with `k ∈ {1, 2, 3}`
because `2e + 2 < 4 (p - 1)`, and accordingly `p` divides `2e + 3`, `2e + 4` or `2e + 5`,
compensating the simple pole of `B_{2e+2}` at `p`. Finally `24` is a `p`-adic unit as `p ≥ 7`.

## Main results

* `Zeta5Irr.norm_prime_mul_bernoulli_two_mul_le_one`: `p B_{2k} ∈ ℤ_p` for every `k`.
* `Zeta5Irr.prime_dvd_moment_factors`: `p ∣ (2e + 3)(2e + 4)(2e + 5)` when `(p - 1) ∣ 2e + 2`.
* `Zeta5Irr.norm_bernoulliMoment_le_one`: `m(e) ∈ ℤ_p` for `p ≥ 7` and `e < 2p - 3`.
* `Zeta5Irr.norm_momentFunctional_X_pow_le_one`: `μ(t ^ e) ∈ ℤ_p` under the same hypotheses, and
  `Zeta5Irr.exists_padicInt_eq_momentFunctional_X_pow`, its form as an element of `ℤ_[p]`.

## Implementation notes

Membership in `ℤ_p` is stated as `‖(x : ℚ_[p])‖ ≤ 1`, which is how Mathlib defines `ℤ_[p]` as a
subtype of `ℚ_[p]`. The hypothesis `0 ≤ e` of the source is automatic for `e : ℕ`. Rather than
the valuation count `v_p(μ(t ^ e)) ≥ 1 - 1 - 0`, the proof bounds `‖p B_{2e+2}‖ ≤ 1` and writes
`(2e + 3)(2e + 4)(2e + 5) = p c` with `c` a natural number.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

open Finset

namespace Zeta5Irr

/-- For every `k`, `p B_{2k}` is a `p`-adic integer: `B_{2k}` has at most a simple pole at `p`. -/
theorem norm_prime_mul_bernoulli_two_mul_le_one (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    ‖(p * bernoulli (2 * k) : ℚ_[p])‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_mul, Padic.norm_p, inv_mul_le_iff₀ hp0, mul_one]
  exact norm_bernoulli_le _

/-- Under `p ≥ 7` and `e < 2p - 3`, the prime `p` divides `(2e + 3)(2e + 4)(2e + 5)` as soon as
`(p - 1) ∣ 2e + 2`: writing `2e + 2 = k (p - 1)`, one has `k ∈ {1, 2, 3}` and then `p` divides
`2e + 3`, `2e + 4` or `2e + 5` respectively. -/
theorem prime_dvd_moment_factors {p e : ℕ} (hp : 7 ≤ p) (he : e < 2 * p - 3)
    (h : (p - 1) ∣ 2 * e + 2) : p ∣ (2 * e + 3) * (2 * e + 4) * (2 * e + 5) := by
  obtain ⟨k, hk⟩ := h
  have hk4 : k < 4 := by
    by_contra! h4
    have : (p - 1) * 4 ≤ (p - 1) * k := Nat.mul_le_mul_left _ h4
    omega
  interval_cases k
  · omega
  · exact (Dvd.intro_left 1 (by omega)).mul_right _ |>.mul_right _
  · exact (Dvd.intro 2 (by omega)).mul_left _ |>.mul_right _
  · exact (Dvd.intro 3 (by omega)).mul_left _

/-- For a prime `p ≥ 7` and `e < 2p - 3`, the Bernoulli moment
`m(e) = (-1) ^ e B_{2e+2} (2e + 3)(2e + 4)(2e + 5) / 24` is a `p`-adic integer. -/
theorem norm_bernoulliMoment_le_one {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) {e : ℕ}
    (he : e < 2 * p - 3) : ‖(bernoulliMoment e : ℚ_[p])‖ ≤ 1 := by
  have hcast : (bernoulliMoment e : ℚ_[p]) =
      (-1) ^ e * bernoulli (2 * (e + 1)) *
        (((2 * e + 3) * (2 * e + 4) * (2 * e + 5) : ℕ) : ℚ_[p]) / 24 := by
    simp only [bernoulliMoment]
    push_cast
    ring_nf
  have hnat (m : ℕ) : ‖(m : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) m
  rw [hcast, norm_div, norm_twentyFour_eq_one (by omega), div_one]
  by_cases h : (p - 1) ∣ 2 * (e + 1)
  · obtain ⟨c, hc⟩ := prime_dvd_moment_factors hp7 he (by rwa [mul_add, mul_one] at h)
    rw [hc, Nat.cast_mul, show ∀ a b x y : ℚ_[p], a * b * (x * y) = a * (x * b) * y by
      intros; ring, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact (mul_le_mul (norm_prime_mul_bernoulli_two_mul_le_one p (e + 1)) (hnat c)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact (mul_le_mul (norm_bernoulli_two_mul_le_one h) (hnat _) (norm_nonneg _)
      zero_le_one).trans_eq (one_mul 1)

/-- **The moments of `μ` in the outer range are `p`-adic integers.** For a prime `p ≥ 7` and
`0 ≤ e < 2p - 3`, `μ(t ^ e) ∈ ℤ_p`. -/
@[zeta5irr "lem_out_moment_int"]
theorem norm_momentFunctional_X_pow_le_one {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) {e : ℕ}
    (he : e < 2 * p - 3) : ‖(momentFunctional (Polynomial.X ^ e) : ℚ_[p])‖ ≤ 1 := by
  rw [momentFunctional_X_pow]
  exact norm_bernoulliMoment_le_one hp7 he

/-- For a prime `p ≥ 7` and `0 ≤ e < 2p - 3`, `μ(t ^ e)` is the image of a `p`-adic integer. -/
theorem exists_padicInt_eq_momentFunctional_X_pow {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) {e : ℕ}
    (he : e < 2 * p - 3) :
    ∃ x : ℤ_[p], (x : ℚ_[p]) = momentFunctional (Polynomial.X ^ e) :=
  ⟨⟨_, norm_momentFunctional_X_pow_le_one hp7 he⟩, rfl⟩

end Zeta5Irr
