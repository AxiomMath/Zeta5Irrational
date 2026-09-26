/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Kappa
public import Zeta5Irr.LocalEstimates.OutMomentInt

/-!
# The low weights `κ_d` are `p`-adic integers

Let `p ≥ 5` be a prime. For `0 ≤ d ≤ p + 1` the weight
`κ_d = d (d - 1) (d - 2) B_{d-3} / 24` lies in `ℤ_p`. The factor `d (d - 1) (d - 2)` is an
integer and `24 = 2^3 · 3` is a `p`-adic unit, so it suffices that `B_m ∈ ℤ_p` for
`m = d - 3 ≤ p - 2`. This is clear for `B_0 = 1`, `B_1 = -1/2` (as `p` is odd) and `B_m = 0`
for odd `m ≥ 3`; for even `m = 2k > 0` one has `0 < 2k < p - 1`, so `(p - 1) ∤ 2k` and the
theorem of von Staudt–Clausen shows that `B_{2k}` is a `p`-adic integer.

## Main results

* `Zeta5Irr.norm_bernoulli_le_one`: `‖B_m‖_p ≤ 1` for a prime `p ≥ 3` and `m ≤ p - 2`.
* `Zeta5Irr.norm_kappa_le_one`: `‖κ_d‖_p ≤ 1` for a prime `p ≥ 5` and `d ≤ p + 1`.
* `Zeta5Irr.exists_padicInt_eq_kappa`: `κ_d` is the image of a `p`-adic integer under the same
  hypotheses.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

/-- For an odd prime `p` and `m ≤ p - 2`, the Bernoulli number `B_m` is a `p`-adic integer. -/
theorem norm_bernoulli_le_one {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {m : ℕ}
    (hm : m ≤ p - 2) : ‖(bernoulli m : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    refine norm_bernoulli_two_mul_le_one fun h => ?_
    have := Nat.le_of_dvd (by omega) h
    omega
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h2 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
        rw [Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes hp.out Nat.prime_two).2 (by omega)
      simp only [mul_zero, zero_add, bernoulli_one]
      push_cast at h2 ⊢
      simp [h2]
    · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one k) (by omega)]
      simp

/-- For a prime `p ≥ 5` and `d ≤ p + 1`, the weight `κ_d` is a `p`-adic integer:
its `p`-adic norm is at most one. -/
@[zeta5irr "lem_kappa_int"]
theorem norm_kappa_le_one {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {d : ℕ} (hd : d ≤ p + 1) :
    ‖(kappa d : ℚ_[p])‖ ≤ 1 := by
  have h24 := norm_twentyFour_eq_one (p := p) hp5
  have hB := norm_bernoulli_le_one (p := p) (by omega) (m := d - 3) (by omega)
  have hc : ‖((d.descFactorial 3 : ℕ) : ℚ_[p])‖ ≤ 1 := by
    exact_mod_cast Padic.norm_int_le_one (p := p) (d.descFactorial 3)
  rw [kappa]
  push_cast at h24 ⊢
  rw [norm_div, norm_mul, h24, div_one]
  simpa using mul_le_mul hc hB (norm_nonneg _) zero_le_one

/-- For a prime `p ≥ 5` and `d ≤ p + 1`, the weight `κ_d` is the image of a `p`-adic
integer. -/
@[zeta5irr "lem_kappa_int"]
theorem exists_padicInt_eq_kappa {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {d : ℕ}
    (hd : d ≤ p + 1) : ∃ x : ℤ_[p], (x : ℚ_[p]) = kappa d :=
  ⟨⟨_, norm_kappa_le_one hp5 hd⟩, rfl⟩

end Zeta5Irr
