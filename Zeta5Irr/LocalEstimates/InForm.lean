/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.Parameters.MuX

/-!
# The inner form

Fix the parameters `N = 3 n` and `K = 40 n`. For `A₁, A₂ ∈ ℚ[t]` the inner form is
`Φ(A₁, A₂) = μ_X(D_N(t) ^ 5 A₁(t) A₂(t); {N + 1, …, K}) ∈ ℚ[X]`,
the rational functional of the far poles `N < j ≤ K` applied to `D_N ^ 5 A₁ A₂`. Since
`μ_X(·; S)` is `ℚ`-linear and multiplication in `ℚ[t]` is commutative, `Φ` is a symmetric
`ℚ`-bilinear form with values in `ℚ[X]`.

## Main definitions

* `Zeta5Irr.innerForm`: `Φ(A₁, A₂) = μ_X(D_N ^ 5 A₁ A₂; {N + 1, …, K})`.

## Implementation notes

* `Φ` is a plain function of two polynomial arguments rather than a bundled bilinear map;
  its bilinearity is used through the `ℚ`-linearity of `μ_X` (see
  `Zeta5Irr.map_mul_gramMatrix_mul_transpose_apply`). The parameters enter through `n`, with
  `N = innerDegree n` and `K = poleBound n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4: the inner range, the distributing basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- The inner form `Φ(A₁, A₂) = μ_X(D_N ^ 5 A₁ A₂; {N + 1, …, K})` with `N = 3 n` and
`K = 40 n`. -/
@[zeta5irr "def_in_form"]
noncomputable def innerForm (n : ℕ) (A₁ A₂ : ℚ[X]) : ℚ[X] :=
  rationalFunctional (Icc (innerDegree n + 1) (poleBound n))
    (poleProductRange (innerDegree n) ℚ ^ 5 * A₁ * A₂)

end Zeta5Irr
