/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MuX

/-!
# Homogeneity of the rational functional

For every finite `S` of positive integers, every `c ∈ ℚ` and every `A ∈ ℚ[t]`,
`μ_X(c A; S) = c μ_X(A; S)`. The quotient of `c A` by the pole product `D_S` is `c` times the
quotient of `A`, the moment functional `μ` is `ℚ`-linear, and each residue term
`A(-j ^ 2) / D_S'(-j ^ 2)` scales by `c`.

## Main results

* `Zeta5Irr.rationalFunctional_smul`: `μ_X(c • A; S) = c • μ_X(A; S)`.
* `Zeta5Irr.rationalFunctional_C_mul`: `μ_X(C c * A; S) = C c * μ_X(A; S)`, the same
  statement with `c A` written as a product of polynomials.

## Implementation notes

* The rational functional is already packaged as a `ℚ`-linear map for each `S`, so both
  statements are instances of `map_smul`; the division argument of the source is carried out
  once, in the construction of that linear map.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The rational functional is homogeneous: `μ_X(c • A; S) = c • μ_X(A; S)`. -/
@[zeta5irr "lem_muX_smul"]
theorem rationalFunctional_smul (S : Finset ℕ) (c : ℚ) (A : ℚ[X]) :
    rationalFunctional S (c • A) = c • rationalFunctional S A :=
  map_smul _ c A

/-- The rational functional is homogeneous, with `c A` written as the product `C c * A`:
`μ_X(C c * A; S) = C c * μ_X(A; S)`. -/
@[zeta5irr "lem_muX_smul"]
theorem rationalFunctional_C_mul (S : Finset ℕ) (c : ℚ) (A : ℚ[X]) :
    rationalFunctional S (C c * A) = C c * rationalFunctional S A := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, rationalFunctional_smul]

end Zeta5Irr
