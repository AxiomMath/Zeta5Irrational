/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauUmbral

/-!
# Reflection invariance of the Bernoulli functional

The Bernoulli functional `L : ℚ[X] → ℚ` (with `L (X ^ k) = B_k`) is invariant under the
reflection `x ↦ -1 - x`: for every `Q : ℚ[X]`, `L (Q (-1 - x)) = L (Q x)`.

By linearity it suffices to treat a monomial `X ^ n`. Then `(-1 - X) ^ n = (-1) ^ n (X + 1) ^ n`,
so by the umbral identity `L ((-1 - X) ^ n) = (-1) ^ n B_n(1)`, and the reflection formula
`B_n(1 - y) = (-1) ^ n B_n(y)` at `y = 0` gives `B_n(1) = (-1) ^ n B_n(0) = (-1) ^ n B_n`.

## Main results

* `Zeta5Irr.bernoulliFunctional_comp_neg_one_sub_X`: `L (Q.comp (-1 - X)) = L Q`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.2 (the reflection and difference identities).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C)

/-- Reflection invariance of the Bernoulli functional: `L (Q (-1 - x)) = L (Q x)` for every
`Q : ℚ[X]`. -/
@[zeta5irr "lem_tau_L_reflect"]
theorem bernoulliFunctional_comp_neg_one_sub_X (Q : ℚ[X]) :
    bernoulliFunctional (Q.comp (-1 - X)) = bernoulliFunctional Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, map_add, map_add, hp, hq]
  | monomial n a =>
    have h : C a * (-1 - X : ℚ[X]) ^ n = (a * (-1) ^ n) • (X + C 1) ^ n := by
      rw [Polynomial.smul_eq_C_mul, map_mul, map_pow, map_neg, map_one, mul_assoc,
        ← mul_pow]
      ring
    have hB : (Polynomial.bernoulli n).eval 1 = (-1) ^ n * bernoulli n := by
      simpa using Polynomial.bernoulli_eval_one_sub n 0
    rw [Polynomial.monomial_comp, h, map_smul, bernoulliFunctional_X_add_C_pow, hB,
      bernoulliFunctional_monomial, smul_eq_mul, mul_assoc, ← mul_assoc ((-1) ^ n), ← mul_pow]
    norm_num

end Zeta5Irr
