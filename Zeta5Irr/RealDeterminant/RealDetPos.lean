/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramDeterminant
public import Zeta5Irr.DegreePositivity.GramPosDef

/-!
# `Δ_K(ξ)` is positive

Let `ξ = ζ(5)`. The real symmetric matrix `G_K(ξ)` is positive definite, so its determinant
is positive. Since evaluation at `ξ` commutes with the determinant, that determinant is
`Δ_K(ξ)`.

## Main results

* `Zeta5Irr.aeval_gramDet_pos`: `0 < Δ_K(ξ)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (the Gram integral and scaling).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- **`Δ_K(ξ)` is positive**, where `ξ = ζ(5)`. -/
@[zeta5irr "lem_real_det_pos"]
theorem aeval_gramDet_pos (n : ℕ) : 0 < aeval zetaFive (gramDet n) := by
  rw [aeval_gramDet]
  exact (posDef_map_aeval_gramMatrix n).det_pos

end Zeta5Irr
