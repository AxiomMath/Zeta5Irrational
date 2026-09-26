/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.BernoulliFunctional
public import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# The umbral identity for the Bernoulli functional

The Bernoulli functional `L : ℚ[X] → ℚ` (with `L (X ^ k) = B_k`) evaluates shifted powers to
Bernoulli polynomials: for every `n` and every `y : ℚ`, `L ((X + y) ^ n) = B_n(y)`. Indeed,
expanding by the binomial theorem gives `∑ₖ (n choose k) B_k y ^ (n - k)`, which is Mathlib's
definition of the Bernoulli polynomial `B_n` evaluated at `y`.

## Main results

* `Zeta5Irr.bernoulliFunctional_X_add_C_pow`:
  `L ((X + C y) ^ n) = (Polynomial.bernoulli n).eval y`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.2 (the reflection and difference identities).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C)

/-- The umbral identity: `L ((X + y) ^ n) = B_n(y)` for every `n` and every `y : ℚ`, where
`L` is the Bernoulli functional and `B_n` is the Bernoulli polynomial. -/
@[zeta5irr "lem_tau_umbral"]
theorem bernoulliFunctional_X_add_C_pow (n : ℕ) (y : ℚ) :
    bernoulliFunctional ((X + C y) ^ n) = (Polynomial.bernoulli n).eval y := by
  rw [add_pow, map_sum, Polynomial.bernoulli, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Polynomial.C_pow, ← Nat.cast_comm, ← Polynomial.C_eq_natCast,
    show C (n.choose k : ℚ) * (X ^ k * C (y ^ (n - k))) =
        C ((n.choose k : ℚ) * y ^ (n - k)) * X ^ k by
      simp only [map_mul]; ring,
    bernoulliFunctional_C_mul_X_pow, Polynomial.eval_monomial]
  ring

end Zeta5Irr
