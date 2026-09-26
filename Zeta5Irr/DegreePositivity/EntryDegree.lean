/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MuX

/-!
# The degree of an entry

For every finite `S` and every `A ∈ ℚ[t]`, the polynomial `μ_X(A; S) ∈ ℚ[X]` has degree at
most one. Indeed `μ_X(A; S) = μ(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X)`, where the
term `μ(P)` is a constant and each pole value `ν_j(X)` is linear in `X`; a constant plus a
finite `ℚ`-linear combination of polynomials of degree at most one has degree at most one.

## Main results

* `Zeta5Irr.natDegree_rationalFunctional_le`: `natDegree (μ_X(A; S)) ≤ 1`.
* `Zeta5Irr.degree_rationalFunctional_le`: `degree (μ_X(A; S)) ≤ 1`.

## Implementation notes

The source takes `S ⊂ ℤ_{>0}`; here `S : Finset ℕ` with no positivity hypothesis, which the
bound does not need.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- `μ_X(A; S)` has degree at most one in `X`. -/
theorem natDegree_rationalFunctional_le (S : Finset ℕ) (A : ℚ[X]) :
    (rationalFunctional S A).natDegree ≤ 1 := by
  rw [rationalFunctional_apply]
  refine natDegree_add_le_of_degree_le ((natDegree_C _).trans_le zero_le_one) ?_
  exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
    (natDegree_C_mul_le _ _).trans (natDegree_poleValue_le j)

/-- `μ_X(A; S)` has degree at most one in `X`. -/
@[zeta5irr "lem_deg_entry"]
theorem degree_rationalFunctional_le (S : Finset ℕ) (A : ℚ[X]) :
    (rationalFunctional S A).degree ≤ 1 :=
  degree_le_of_natDegree_le (natDegree_rationalFunctional_le S A)

end Zeta5Irr
