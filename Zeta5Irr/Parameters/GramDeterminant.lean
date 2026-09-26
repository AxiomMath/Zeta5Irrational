/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramMatrix

/-!
# The determinant `Δ_K`

The polynomial `Δ_K(X) ∈ ℚ[X]` is the determinant of the matrix `G_K(X)`, that is
`Δ_K(X) = det G_K(X)`. Since the determinant is a polynomial in the entries, evaluating
`Δ_K` at an element `x` of a commutative `ℚ`-algebra gives the determinant of the matrix
`G_K(x)` obtained by evaluating every entry of `G_K(X)` at `x`.

## Main definitions

* `Zeta5Irr.gramDet`: the polynomial `Δ_K(X) = det G_K(X)`.

## Main results

* `Zeta5Irr.aeval_gramDet`: `Δ_K(x) = det G_K(x)` for `x` in any commutative `ℚ`-algebra.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The polynomial `Δ_K(X) = det G_K(X) ∈ ℚ[X]`, where `K = 40 n`. -/
@[zeta5irr "def_DeltaK"]
noncomputable def gramDet (n : ℕ) : ℚ[X] :=
  (gramMatrix n).det

/-- Evaluation commutes with the determinant: `Δ_K(x) = det G_K(x)` for `x` in any commutative
`ℚ`-algebra. -/
theorem aeval_gramDet {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ) (x : A) :
    aeval x (gramDet n) = ((gramMatrix n).map (aeval x)).det :=
  (aeval x : ℚ[X] →ₐ[ℚ] A).toRingHom.map_det (gramMatrix n)

end Zeta5Irr
