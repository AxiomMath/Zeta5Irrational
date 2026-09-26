/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.BernoulliFunctional

/-!
# The functional `τ` on polynomials

The functional `τ : ℚ[X] → ℚ` is defined by `τ(P) = L(P''') / 24`, where `P'''` is the third
derivative of `P` and `L` is the Bernoulli functional `X ^ k ↦ B_k`. It is `ℚ`-linear, and on
monomials it is `τ(X ^ d) = d (d - 1) (d - 2) B_{d-3} / 24`, which vanishes for `d ≤ 2`.

## Main definitions

* `Zeta5Irr.tau`: the `ℚ`-linear map `τ : ℚ[X] →ₗ[ℚ] ℚ`, `τ P = L (P''') / 24`.

## Main results

* `Zeta5Irr.tau_apply`: `τ P = L (derivative^[3] P) / 24`.
* `Zeta5Irr.tau_X_pow`: `τ (X ^ d) = d.descFactorial 3 * B_{d-3} / 24`.
* `Zeta5Irr.tau_X_pow_of_le_two`: `τ (X ^ d) = 0` for `d ≤ 2`.
* `Zeta5Irr.iterate_derivative_comp_C_add_C_mul_X`: the chain rule
  `(d/dx)^n P(a + mx) = m^n P^{(n)}(a + mx)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C derivative)

/-- The functional `τ : ℚ[X] →ₗ[ℚ] ℚ`, `τ P = L (P''') / 24`, where `P'''` is the third
derivative of `P` and `L` is the Bernoulli functional `bernoulliFunctional`. -/
@[zeta5irr "def_tau"]
noncomputable def tau : ℚ[X] →ₗ[ℚ] ℚ :=
  (1 / 24 : ℚ) • bernoulliFunctional ∘ₗ derivative ^ 3

/-- The defining formula of `τ`: `τ P = L (P''') / 24`. -/
@[zeta5irr "def_tau"]
theorem tau_apply (P : ℚ[X]) : tau P = bernoulliFunctional (derivative^[3] P) / 24 := by
  simp [tau, Module.End.pow_apply, div_eq_inv_mul]

/-- `τ (X ^ d) = d (d - 1) (d - 2) B_{d-3} / 24`, written with `Nat.descFactorial`. -/
theorem tau_X_pow (d : ℕ) :
    tau (X ^ d) = (d.descFactorial 3 : ℚ) * bernoulli (d - 3) / 24 := by
  rw [tau_apply, Polynomial.iterate_derivative_X_pow_eq_smul, map_smul,
    bernoulliFunctional_X_pow, smul_eq_mul]

/-- `τ (X ^ d) = 0` when `d ≤ 2`, since then the third derivative of `X ^ d` vanishes. -/
theorem tau_X_pow_of_le_two {d : ℕ} (hd : d ≤ 2) : tau (X ^ d) = 0 := by
  rw [tau_X_pow, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
  simp

/-- `τ (C a * X ^ d) = a d (d - 1) (d - 2) B_{d-3} / 24`. -/
theorem tau_C_mul_X_pow (a : ℚ) (d : ℕ) :
    tau (C a * X ^ d) = a * ((d.descFactorial 3 : ℚ) * bernoulli (d - 3) / 24) := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, tau_X_pow, smul_eq_mul]

/-- The chain rule for the iterated derivatives of `P(a + mx)`:
`(d/dx)^n P(a + mx) = m^n P^{(n)}(a + mx)`. -/
theorem iterate_derivative_comp_C_add_C_mul_X {R : Type*} [CommSemiring R] (P : R[X])
    (a m : R) (n : ℕ) :
    derivative^[n] (P.comp (C a + C m * X)) =
      C (m ^ n) * (derivative^[n] P).comp (C a + C m * X) := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Polynomial.derivative_mul,
      Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_comp]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X, zero_add, zero_mul, mul_one, pow_succ, Polynomial.C_mul]
    ring

end Zeta5Irr
