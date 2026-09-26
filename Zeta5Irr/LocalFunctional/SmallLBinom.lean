/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom
public import Zeta5Irr.LocalFunctional.TauLDiff
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star

/-!
# The Bernoulli functional on the binomial polynomials

Let `L : ℚ[x] → ℚ` be the Bernoulli functional, `L (x ^ k) = B_k`. For every `k ≥ 0`,
`L (x choose k) = (-1) ^ k / (k + 1)`.

The proof applies the difference identity `L (P (x + 1)) - L (P x) = P'(0)` to
`P = (x choose (k + 1))`. Pascal's rule `(x + 1 choose k + 1) - (x choose k + 1) = (x choose k)`
identifies the left-hand side with `L (x choose k)`. Writing
`(x choose k + 1) = (1 / (k + 1)!) · x · ∏_{i=1}^{k} (x - i)`, only the term differentiating
the factor `x` survives at `x = 0`, giving
`P'(0) = (1 / (k + 1)!) ∏_{i=1}^{k} (-i) = (-1) ^ k / (k + 1)`.

## Main results

* `Zeta5Irr.qbinom_succ_comp_X_add_one_sub`: Pascal's rule
  `(x + 1 choose k + 1) - (x choose k + 1) = (x choose k)` in `ℚ[x]`.
* `Zeta5Irr.eval_zero_derivative_qbinom_succ`: the derivative of `(x choose k + 1)` at `0` is
  `(-1) ^ k / (k + 1)`.
* `Zeta5Irr.bernoulliFunctional_qbinom`: `L (x choose k) = (-1) ^ k / (k + 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Nat

/-- Pascal's rule for the binomial polynomials:
`(x + 1 choose k + 1) - (x choose k + 1) = (x choose k)`. -/
theorem qbinom_succ_comp_X_add_one_sub (k : ℕ) :
    (qbinom (k + 1)).comp (X + 1) - qbinom (k + 1) = qbinom k := by
  have h1 : (descPochhammer ℚ (k + 1)).comp (X + 1) = (X + 1) * descPochhammer ℚ k := by
    rw [descPochhammer_succ_left, mul_comp, comp_assoc, X_comp]
    simp
  have h2 := descPochhammer_succ_right ℚ k
  rw [qbinom, qbinom, smul_comp, h1, h2, ← smul_sub]
  rw [show (X + 1) * descPochhammer ℚ k - descPochhammer ℚ k * (X - (k : ℚ[X])) =
      ((k + 1 : ℚ)) • descPochhammer ℚ k by
    rw [Polynomial.smul_eq_C_mul]; simp; ring]
  rw [smul_smul, Nat.factorial_succ]
  congr 1
  push_cast
  field_simp

/-- The derivative of `(x choose k + 1)` at `x = 0` is `(-1) ^ k / (k + 1)`. -/
theorem eval_zero_derivative_qbinom_succ (k : ℕ) :
    (qbinom (k + 1)).derivative.eval 0 = (-1) ^ k / (k + 1) := by
  rw [qbinom, derivative_smul, descPochhammer_succ_left, derivative_mul, eval_smul]
  simp only [derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero,
    eval_comp, eval_sub, eval_one, zero_sub, descPochhammer_eval_eq_prod_range, smul_eq_mul]
  have : ∏ i ∈ Finset.range k, (-1 - (i : ℚ)) = (-1) ^ k * k ! := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
      show ((-1 : ℚ)) ^ k = ∏ _i ∈ Finset.range k, (-1 : ℚ) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast; ring
  rw [this, Nat.factorial_succ]
  push_cast
  field_simp

/-- The Bernoulli functional on the binomial basis: `L (x choose k) = (-1) ^ k / (k + 1)`. -/
@[zeta5irr "lem_small_L_binom"]
theorem bernoulliFunctional_qbinom (k : ℕ) :
    bernoulliFunctional (qbinom k) = (-1) ^ k / (k + 1) := by
  rw [← qbinom_succ_comp_X_add_one_sub, map_sub, bernoulliFunctional_comp_X_add_one_sub,
    eval_zero_derivative_qbinom_succ]

end Zeta5Irr
