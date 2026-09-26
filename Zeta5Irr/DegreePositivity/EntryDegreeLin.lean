/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MuX

/-!
# The coefficient of `X` in the rational functional

For every finite `S ⊂ ℤ_{>0}` and every `A ∈ ℚ[t]`, the coefficient of `X` in `μ_X(A; S)` is
`∑_{j ∈ S} A(-j ^ 2) j ^ 4 / D_S'(-j ^ 2)`.

In the defining formula `μ_X(A; S) = μ(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X)` the
term `μ(P)` is a constant, and the coefficient of `X` in the pole value `ν_j(X)` is `j ^ 4`;
taking the coefficient of `X` is `ℚ`-linear.

## Main results

* `Zeta5Irr.coeff_one_rationalFunctional`: the coefficient of `X` in `μ_X(A; S)`.

## Implementation notes

* The source takes `S ⊂ ℤ_{>0}`; here `S : Finset ℕ` with no positivity hypothesis, which
  the statement does not need.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The coefficient of `X` in `μ_X(A; S)` is `∑_{j ∈ S} A(-j ^ 2) j ^ 4 / D_S'(-j ^ 2)`. -/
@[zeta5irr "lem_deg_entry_lin"]
theorem coeff_one_rationalFunctional (S : Finset ℕ) (A : ℚ[X]) :
    (rationalFunctional S A).coeff 1 =
      ∑ j ∈ S, A.eval (-(j : ℚ) ^ 2) * (j : ℚ) ^ 4 /
        (derivative (poleProduct S ℚ)).eval (-(j : ℚ) ^ 2) := by
  rw [rationalFunctional_apply, coeff_add, coeff_C_of_ne_zero one_ne_zero, zero_add,
    finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, coeff_one_poleValue, div_mul_eq_mul_div]

end Zeta5Irr
