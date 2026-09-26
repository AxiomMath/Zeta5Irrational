/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramMatrix
public import Zeta5Irr.LocalEstimates.OutGcirc

/-!
# The correction matrix of the outer range

Let `p` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. The correction
matrix is the `h × h` matrix over `ℚ_p[X]`
`𝓛_p = p (G_K - G_K^∘)`,
the difference between the matrix `G_K` and the Gram matrix `G_K^∘` of the integral part of the
outer form, scaled by `p`. Both summands are symmetric, hence so is `𝓛_p`.

## Main definitions

* `Zeta5Irr.outerCorrectionMatrix`: the matrix `𝓛_p`.

## Main results

* `Zeta5Irr.outerCorrectionMatrix_apply`: `(𝓛_p)_{kl} = p ((G_K)_{kl} - (G_K^∘)_{kl})`.
* `Zeta5Irr.outerCorrectionMatrix_isSymm`, `Zeta5Irr.outerCorrectionMatrix_transpose`:
  `𝓛_p` is symmetric.

## Implementation notes

* `G_K` has entries in `ℚ[X]`; it is regarded as a matrix over `ℚ_p[X]` by applying
  `Polynomial.map (algebraMap ℚ ℚ_[p])` entrywise.
* `𝓛_p` is the scalar multiple `(p : ℚ_[p]) • (G_K - G_K^∘)` in the `ℚ_[p]`-module of
  matrices, so the entrywise lemmas `Matrix.smul_apply` and `Matrix.sub_apply` apply directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The correction matrix `𝓛_p = p (G_K - G_K^∘)`, an `h × h` matrix over `ℚ_p[X]`, where
`G_K` is viewed over `ℚ_p[X]` through the embedding `ℚ[X] → ℚ_p[X]`. -/
@[zeta5irr "def_out_Lcorr"]
noncomputable def outerCorrectionMatrix :
    Matrix (Fin (matrixOrder n)) (Fin (matrixOrder n)) ℚ_[p][X] :=
  (p : ℚ_[p]) • ((gramMatrix n).map (Polynomial.map (algebraMap ℚ ℚ_[p])) -
    outerIntegralGramMatrix p n)

/-- The entries of `𝓛_p`: `(𝓛_p)_{kl} = p ((G_K)_{kl} - (G_K^∘)_{kl})`. -/
theorem outerCorrectionMatrix_apply (k l : Fin (matrixOrder n)) :
    outerCorrectionMatrix p n k l =
      (p : ℚ_[p]) • ((gramMatrix n k l).map (algebraMap ℚ ℚ_[p]) -
        outerIntegralGramMatrix p n k l) :=
  rfl

/-- `𝓛_p` is symmetric. -/
theorem outerCorrectionMatrix_isSymm : (outerCorrectionMatrix p n).IsSymm :=
  (((gramMatrix_isSymm n).map _).sub (outerIntegralGramMatrix_isSymm p n)).smul _

/-- `𝓛_pᵀ = 𝓛_p`. -/
@[simp]
theorem outerCorrectionMatrix_transpose :
    (outerCorrectionMatrix p n).transpose = outerCorrectionMatrix p n :=
  outerCorrectionMatrix_isSymm p n

end Zeta5Irr
