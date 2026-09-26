/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MuX

/-!
# Additivity of the rational functional

For every finite set `S` of positive integers and all `A₁, A₂ ∈ ℚ[t]`,
`μ_X(A₁ + A₂; S) = μ_X(A₁; S) + μ_X(A₂; S)`. The three ingredients of `μ_X` are each
additive in `A`: the quotient of Euclidean division by the monic `D_S` (by uniqueness of
division), the moment functional `μ`, and the evaluations `A ↦ A(-j ^ 2)`.

## Main results

* `Zeta5Irr.rationalFunctional_add`: `μ_X(A₁ + A₂; S) = μ_X(A₁; S) + μ_X(A₂; S)`.

## Implementation notes

* The rational functional is packaged as a `ℚ`-linear map `ℚ[t] →ₗ[ℚ] ℚ[X]` for each `S`,
  and the additivity argument above is carried out once, in the construction of that map.
  The present statement is therefore `map_add` of the linear map.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

/-- The rational functional is additive: `μ_X(A₁ + A₂; S) = μ_X(A₁; S) + μ_X(A₂; S)`. -/
@[zeta5irr "lem_muX_add"]
theorem rationalFunctional_add (S : Finset ℕ) (A₁ A₂ : Polynomial ℚ) :
    rationalFunctional S (A₁ + A₂) = rationalFunctional S A₁ + rationalFunctional S A₂ :=
  map_add _ _ _

end Zeta5Irr
