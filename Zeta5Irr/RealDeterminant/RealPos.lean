/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.NormalizedDeterminant
public import Zeta5Irr.RealDeterminant.RealDetPos

/-!
# `F_K(ξ)` is positive

Let `ξ = ζ(5)`. The normalized determinant is `F_K(X) = S_K Δ_K(X)`, where the scaling
factor `S_K` is a quotient of products of positive integers, hence positive, and
`Δ_K(ξ) > 0` since `G_K(ξ)` is positive definite. Hence `F_K(ξ) > 0`.

## Main results

* `Zeta5Irr.aeval_normalizedDet`: `F_K(x) = S_K Δ_K(x)` for every real `x`.
* `Zeta5Irr.aeval_normalizedDet_pos`: `0 < F_K(ξ)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (the Gram integral and scaling).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- Evaluation of `F_K` at a real number: `F_K(x) = S_K Δ_K(x)`. -/
@[simp]
theorem aeval_normalizedDet (n : ℕ) (x : ℝ) :
    aeval x (normalizedDet n) = (scalingFactor n : ℝ) * aeval x (gramDet n) := by
  simp [normalizedDet]

/-- **`F_K(ξ)` is positive**, where `ξ = ζ(5)`. -/
@[zeta5irr "prop_real_pos"]
theorem aeval_normalizedDet_pos (n : ℕ) : 0 < aeval zetaFive (normalizedDet n) := by
  rw [aeval_normalizedDet]
  exact mul_pos (by exact_mod_cast scalingFactor_pos n) (aeval_gramDet_pos n)

end Zeta5Irr
