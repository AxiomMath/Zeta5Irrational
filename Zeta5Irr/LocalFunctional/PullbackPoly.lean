/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MomentFunctional
public import Zeta5Irr.LocalFunctional.TauMonomial
public import Mathlib.RingTheory.PiTensorProduct

/-!
# The pullback identity

The moment functional `μ : ℚ[t] → ℚ` is the pullback of the functional
`τ(P) = L(P''') / 24` along the substitution `A ↦ x ^ 5 A(-x ^ 2)`:
for every `A ∈ ℚ[t]`, `μ(A) = τ(x ^ 5 A(-x ^ 2))`.

Both sides are `ℚ`-linear in `A`, so it suffices to check the identity on the monomials
`t ^ e`. There `x ^ 5 (-x ^ 2) ^ e = (-1) ^ e x ^ (2e + 5)`, and
`τ(x ^ (2e + 5)) = κ_{2e+5} = (2e + 5)(2e + 4)(2e + 3) B_{2e+2} / 24`, so the right-hand side
is `(-1) ^ e κ_{2e+5} = m(e) = μ(t ^ e)`.

## Main results

* `Zeta5Irr.momentFunctional_eq_tau_pullback`: `μ(A) = τ(x ^ 5 A(-x ^ 2))`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.3 (the pullback identity).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The pullback identity: for every `A ∈ ℚ[t]`, `μ(A) = τ(x ^ 5 A(-x ^ 2))`. -/
@[zeta5irr "lem_pullback_poly"]
theorem momentFunctional_eq_tau_pullback (A : ℚ[X]) :
    momentFunctional A = tau (X ^ 5 * A.comp (-X ^ 2)) := by
  induction A using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, mul_add, hp, hq]
  | monomial e c =>
    have h : (X ^ 5 * (monomial e c).comp (-X ^ 2) : ℚ[X]) =
        C (c * (-1) ^ e) * X ^ (2 * e + 5) := by
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, ← pow_mul,
        C_mul, C_pow, C_neg, C_1]
      ring
    rw [h, ← smul_eq_C_mul, map_smul, tau_X_pow_eq_kappa, smul_eq_mul,
      momentFunctional_monomial, bernoulliMoment,
      show 2 * e + 5 = (2 * e + 2) + 3 by ring, kappa_add_three]
    push_cast
    ring

end Zeta5Irr
