/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutForm0

/-!
# The Gram matrix of the integral part of the outer form

Let `p` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. The matrix
`G_K^∘` is the `h × h` matrix over `ℚ_p[X]` with entries
`(G_K^∘)_{kl} = Φ₀(t ^ k, t ^ l)` for `0 ≤ k, l < h`, where `Φ₀` is the integral part of the
outer form. It is the Gram matrix of `Φ₀` on the monomial basis `1, t, …, t ^ (h - 1)`; since
`Φ₀` is symmetric, so is `G_K^∘`.

## Main definitions

* `Zeta5Irr.outerIntegralGramMatrix`: the matrix `G_K^∘`.

## Main results

* `Zeta5Irr.outerIntegralGramMatrix_apply`: `(G_K^∘)_{kl} = Φ₀(t ^ k, t ^ l)`.
* `Zeta5Irr.outerIntegralGramMatrix_isSymm`, `Zeta5Irr.outerIntegralGramMatrix_transpose`:
  `G_K^∘` is symmetric.

## Implementation notes

* The rows and columns are indexed by `Fin h` with `h = matrixOrder n`, and `t ^ k` is the
  monomial `X ^ (k : ℕ)` in `ℚ[X]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The matrix `G_K^∘`: the `h × h` matrix over `ℚ_p[X]` with entries
`(G_K^∘)_{kl} = Φ₀(t ^ k, t ^ l)` for `0 ≤ k, l < h`, where `h = 37 n`. -/
@[zeta5irr "def_out_Gcirc"]
noncomputable def outerIntegralGramMatrix :
    Matrix (Fin (matrixOrder n)) (Fin (matrixOrder n)) ℚ_[p][X] :=
  Matrix.of fun k l => outerIntegralForm p n (X ^ (k : ℕ)) (X ^ (l : ℕ))

/-- The entries of `G_K^∘`: `(G_K^∘)_{kl} = Φ₀(t ^ k, t ^ l)`. -/
@[simp]
theorem outerIntegralGramMatrix_apply (k l : Fin (matrixOrder n)) :
    outerIntegralGramMatrix p n k l = outerIntegralForm p n (X ^ (k : ℕ)) (X ^ (l : ℕ)) :=
  rfl

/-- `G_K^∘` is symmetric. -/
theorem outerIntegralGramMatrix_isSymm : (outerIntegralGramMatrix p n).IsSymm :=
  Matrix.IsSymm.ext fun k l => by
    simp only [outerIntegralGramMatrix_apply, outerIntegralForm_comm p n (X ^ (k : ℕ))]

/-- `(G_K^∘)ᵀ = G_K^∘`. -/
@[simp]
theorem outerIntegralGramMatrix_transpose :
    (outerIntegralGramMatrix p n).transpose = outerIntegralGramMatrix p n :=
  outerIntegralGramMatrix_isSymm p n

end Zeta5Irr
