/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.BernoulliFunctional
public import Zeta5Irr.LocalFunctional.TauUmbral

/-!
# The difference identity for the Bernoulli functional

Let `L : ℚ[X] → ℚ` be the Bernoulli functional, `L (X ^ k) = B_k`. For every polynomial `P`,
`L (P (X + 1)) - L (P X) = P'(0)`. Both sides are linear in `P`, so it suffices to check
`P = X ^ n`; there the umbral identity gives `L ((X + 1) ^ n) - L (X ^ n) = B_n(1) - B_n(0)`,
and the difference equation of the Bernoulli polynomials gives `B_n(1) - B_n(0) = n 0 ^ (n - 1)`,
which is the derivative of `X ^ n` at `0`.

## Main results

* `Zeta5Irr.bernoulliFunctional_comp_X_add_one_sub`:
  `L (P.comp (X + 1)) - L P = P.derivative.eval 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.2 (the reflection and difference identities).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C)

/-- The umbral monomial case: `L ((X + 1) ^ n) - L (X ^ n) = n 0 ^ (n - 1)`, the derivative of
`X ^ n` at `0`. -/
theorem bernoulliFunctional_X_add_one_pow_sub (n : ℕ) :
    bernoulliFunctional ((X + 1) ^ n) - bernoulliFunctional (X ^ n) =
      (n : ℚ) * 0 ^ (n - 1) := by
  have h := congrArg (Polynomial.eval 0) (Polynomial.bernoulli_comp_one_add_X n)
  have h1 := bernoulliFunctional_X_add_C_pow n 1
  have h0 := bernoulliFunctional_X_add_C_pow n 0
  simp only [map_one, map_zero, add_zero] at h1 h0
  rw [h1, h0]
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
    add_zero, nsmul_eq_mul] at h
  simp [h]

/-- The difference identity for the Bernoulli functional: for every `P : ℚ[X]`,
`L (P (X + 1)) - L (P X) = P'(0)`. -/
@[zeta5irr "lem_tau_L_diff"]
theorem bernoulliFunctional_comp_X_add_one_sub (P : ℚ[X]) :
    bernoulliFunctional (P.comp (X + 1)) - bernoulliFunctional P = P.derivative.eval 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.add_comp, map_add, Polynomial.eval_add]
    rw [← hp, ← hq]
    ring
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp, Polynomial.derivative_C_mul_X_pow, ← Polynomial.smul_eq_C_mul,
      ← Polynomial.smul_eq_C_mul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub,
      bernoulliFunctional_X_add_one_pow_sub]
    simp only [Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring

end Zeta5Irr
