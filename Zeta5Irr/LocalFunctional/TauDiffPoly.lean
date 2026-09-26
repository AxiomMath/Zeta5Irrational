/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauX
public import Zeta5Irr.LocalFunctional.TauLDiff
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The difference identity for `τ_X` without poles

For every `P ∈ ℚ[x]`, `τ_X(P(x + 1) - P(x); ∅)` is the coefficient of `x ^ 4` in `P`.
With no poles, `E_∅ = 1` and `τ_X(Q; ∅) = τ(Q) = L(Q''') / 24`. Differentiation commutes with
the shift `x ↦ x + 1`, so the difference identity `L(Q(x + 1)) - L(Q(x)) = Q'(0)` for the
Bernoulli functional, applied to `Q = P'''`, gives `P⁗(0) / 24 = [x ^ 4] P`.

## Main results

* `Zeta5Irr.tauX_empty`: `τ_X(A; ∅) = τ(A)`.
* `Zeta5Irr.tau_comp_X_add_one_sub`: `τ(P(x + 1)) - τ(P) = [x ^ 4] P`.
* `Zeta5Irr.tauX_empty_comp_X_add_one_sub`: `τ_X(P(x + 1) - P(x); ∅) = [x ^ 4] P`.

## Implementation notes

The target of `τ_X` is `ℚ[X]`, so the coefficient `[x ^ 4] P` appears as the constant
polynomial `C (P.coeff 4)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.2 (the reflection and difference identities).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C derivative)

/-- With no poles, `τ_X(A; ∅) = τ(A)`, since `E_∅ = 1`. -/
@[simp]
theorem tauX_empty (A : ℚ[X]) : tauX ∅ A = C (tau A) := by
  simp [tauX]

/-- The difference identity for `τ`: `τ(P(x + 1)) - τ(P(x))` is the coefficient of `x ^ 4`
in `P`. -/
theorem tau_comp_X_add_one_sub (P : ℚ[X]) :
    tau (P.comp (X + 1)) - tau P = P.coeff 4 := by
  have hcomm (n : ℕ) (Q : ℚ[X]) :
      derivative^[n] (Q.comp (X + 1)) = (derivative^[n] Q).comp (X + 1) := by
    simpa [add_comm] using iterate_derivative_comp_C_add_C_mul_X Q 1 1 n
  rw [tau_apply, tau_apply, hcomm, ← sub_div, bernoulliFunctional_comp_X_add_one_sub,
    ← Function.iterate_succ_apply' derivative, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial]

/-- **The difference identity for `τ_X` without poles**: for every `P ∈ ℚ[x]`,
`τ_X(P(x + 1) - P(x); ∅)` is the coefficient of `x ^ 4` in `P`. -/
@[zeta5irr "lem_tau_diff_poly"]
theorem tauX_empty_comp_X_add_one_sub (P : ℚ[X]) :
    tauX ∅ (P.comp (X + 1) - P) = C (P.coeff 4) := by
  rw [tauX_empty, map_sub, tau_comp_X_add_one_sub]

end Zeta5Irr
