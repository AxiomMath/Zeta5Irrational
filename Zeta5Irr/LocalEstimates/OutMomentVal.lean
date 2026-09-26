/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MomentFunctional
public import Zeta5Irr.LocalFunctional.KappaVal
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The moments `μ(t ^ e)` have `p`-adic valuation at least `-1`

Let `p ≥ 7` be a prime and `e ≥ 0`. The moment
`μ(t ^ e) = (-1) ^ e B_{2e+2} (2e + 3)(2e + 4)(2e + 5) / 24` equals `(-1) ^ e κ_{2e+5}`, where
`κ_d = d (d - 1)(d - 2) B_{d-3} / 24`. Since `(-1) ^ e` is a `p`-adic unit, the bound
`v_p(κ_d) ≥ -1` gives `v_p(μ(t ^ e)) ≥ -1`.

## Main results

* `Zeta5Irr.bernoulliMoment_eq_neg_one_pow_mul_kappa`: `m(e) = (-1) ^ e κ_{2e+5}`.
* `Zeta5Irr.momentFunctional_X_pow_eq_neg_one_pow_mul_kappa`: `μ(t ^ e) = (-1) ^ e κ_{2e+5}`.
* `Zeta5Irr.neg_one_le_padicValRat_momentFunctional_X_pow`: `v_p(μ(t ^ e)) ≥ -1`.

## Implementation notes

The valuation is `padicValRat`, which assigns `0` to `0`; the bound is then trivial at `0`.
The source assumes `p ≥ 7`; the argument only uses the bound on `κ_d`, valid for `p ≥ 5`, so
the result is stated under `5 ≤ p`, a generalization. The hypothesis `0 ≤ e` is automatic for
`e : ℕ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7 (The outer range: the integral part and its
  correction).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- The Bernoulli moment is a signed weight: `m(e) = (-1) ^ e κ_{2e+5}`. -/
theorem bernoulliMoment_eq_neg_one_pow_mul_kappa (e : ℕ) :
    bernoulliMoment e = (-1) ^ e * kappa (2 * e + 5) := by
  rw [show 2 * e + 5 = (2 * e + 2) + 3 by ring, kappa_add_three, bernoulliMoment]
  push_cast
  ring

/-- `μ(t ^ e) = (-1) ^ e κ_{2e+5}`. -/
theorem momentFunctional_X_pow_eq_neg_one_pow_mul_kappa (e : ℕ) :
    momentFunctional (X ^ e) = (-1) ^ e * kappa (2 * e + 5) := by
  rw [momentFunctional_X_pow, bernoulliMoment_eq_neg_one_pow_mul_kappa]

/-- **The moments of `μ` have at most a simple pole at `p`.** For a prime `p ≥ 5` (in the
source, `p ≥ 7`) and every `e ≥ 0`, `v_p(μ(t ^ e)) ≥ -1`. -/
@[zeta5irr "lem_out_moment_val"]
theorem neg_one_le_padicValRat_momentFunctional_X_pow {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e : ℕ) : -1 ≤ padicValRat p (momentFunctional (X ^ e)) := by
  rw [momentFunctional_X_pow_eq_neg_one_pow_mul_kappa]
  by_cases h : kappa (2 * e + 5) = 0
  · simp [h]
  have hs : padicValRat p ((-1) ^ e) = 0 := by
    rcases neg_one_pow_eq_or ℚ e with hs | hs <;> simp [hs]
  rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) h, hs, zero_add]
  exact neg_one_le_padicValRat_kappa hp5 (2 * e + 5)

end Zeta5Irr
