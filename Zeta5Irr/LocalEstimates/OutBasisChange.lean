/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutUnimodular
public import Zeta5Irr.LocalEstimates.InBasisChange

/-!
# The outer basis change does not move the valuation

Let `K = 40 n` and let `p` be a prime with `p ≥ 7`, `p ≤ K < 3p`, `p² > 2K`, `2N < p` and
`5N ≤ 2p - 2`. Then `v_p^G(det (C^out G_K (C^out)ᵀ)) = v_p^G(Δ_K)`.

Indeed, `C^out` is square, so `det (C^out G_K (C^out)ᵀ) = (det C^out)² Δ_K`; since `det C^out`
is a unit of `ℤ_p`, multiplying by its square does not change the Gauss valuation.

## Main results

* `Zeta5Irr.vpG_map_det_outerCoeffMatrix_mul_gramMatrix_mul_transpose`:
  `v_p^G(det (C^out G_K (C^out)ᵀ)) = v_p^G(Δ_K)`.

## Implementation notes

* `C^out` is rectangular in Lean, with rows indexed by the pairs `(a, i)` and columns by
  `Fin h`; the product `C^out G_K (C^out)ᵀ` is square with rows and columns indexed by the
  pairs, so its determinant needs no identification of index types. The matrix `C^out` is taken
  over `ℚ[X]`, where it has constant entries, and the Gauss valuation of a polynomial in `ℚ[X]`
  is that of its image in `ℚ_p[X]`.
* The result is proved under the weaker hypotheses that `p` is an odd prime with `p ≤ K`; the
  remaining hypotheses of the source are not needed. The parametrisation `K = 40 n`, `N = 3 n`,
  `h = 37 n` is built in.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.12 (The outer range: the conjugated decomposition).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

variable {p : ℕ} {n : ℕ}

/-- **The outer basis change does not move the valuation** (§5.12). For an odd prime `p` with
`p ≤ K = 40 n`, `v_p^G(det (C^out G_K (C^out)ᵀ)) = v_p^G(Δ_K)`. -/
@[zeta5irr "lem_out_basis_change"]
theorem vpG_map_det_outerCoeffMatrix_mul_gramMatrix_mul_transpose [Fact p.Prime] (hp : Odd p)
    (hK : p ≤ poleBound n) :
    vpG ((outerCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        gramMatrix n *
        (outerCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose).det.map
        (Rat.castHom ℚ_[p])) =
      vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  rw [← map_intCast_outerCoeffMatrix]
  exact vpG_map_det_map_intCast_mul_gramMatrix_mul_transpose _
    (Fintype.equivFinOfCardEq (card_outerCoeffMatrix_rows_eq_matrixOrder hp n))
    (isUnit_det_outerCoeffMatrix hp hK _)

end Zeta5Irr
