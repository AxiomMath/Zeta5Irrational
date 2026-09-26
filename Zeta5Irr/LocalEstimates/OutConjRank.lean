/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutLcorr
public import Zeta5Irr.LocalEstimates.OutRank
public import Zeta5Irr.LocalEstimates.OutV
public import Zeta5Irr.LocalEstimates.Rp

/-!
# The outer range: the rank of the conjugated correction

Let `p` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. Conjugating the
correction matrix `𝓛_p = p (G_K - G_K^∘)` by the outer coefficient matrix `C^out` does not
increase its rank: `rank_{ℚ_p} (C^out 𝓛_p (C^out)ᵀ) ≤ rank_{ℚ_p} 𝓛_p ≤ r_p`, where
`r_p = max(0, K + 4 N - 2 p + 2)`.

## Main results

* `Zeta5Irr.rank_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_le`:
  `rank_{ℚ_p} (C^out 𝓛_p (C^out)ᵀ) ≤ r_p`, the entries of `𝓛_p` being read in `ℚ_p` through
  their constant coefficients.
* `Zeta5Irr.rank_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_le_polynomial`: the
  same bound for the product taken over `ℚ_p[X]`.

## Implementation notes

* The source deduces the bound from the equality
  `rank (C^out 𝓛_p (C^out)ᵀ) = rank 𝓛_p`, which holds because `det C^out` is a unit of `ℤ_p`.
  For the inequality only `rank (A B) ≤ rank A` and `rank (A B) ≤ rank B` are needed, so the
  unimodularity of `C^out` and the hypotheses `K ∈ 40 ℤ_{>0}`, `p ≥ 7`, `p ≤ K < 3 p`,
  `p² > 2 K`, `2 N < p` and `5 N ≤ 2 p - 2` of the source are not used: the bound holds for
  every prime `p`. In particular `C^out` need not be square.
* The entries of `𝓛_p` are constants of `ℚ_p[X]`; as in `lem_out_rank` they are read in `ℚ_p`
  by applying `Polynomial.constantCoeff` entrywise, and `C^out` is taken over `ℚ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.12: the outer range, the conjugated decomposition.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **The rank of the conjugated correction** (§5.12). For a prime `p`,
`rank_{ℚ_p} (C^out 𝓛_p (C^out)ᵀ) ≤ r_p`, where the entries of `𝓛_p` are read in `ℚ_p` through
their constant coefficients and `r_p = max(0, K + 4 N - 2 p + 2)`. -/
@[zeta5irr "lem_out_conj_rank"]
theorem rank_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_le (n : ℕ) :
    (outerCoeffMatrix ℚ_[p] p (innerDegree n) (poleBound n) (matrixOrder n) *
        (outerCorrectionMatrix p n).map constantCoeff *
        (outerCoeffMatrix ℚ_[p] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose).rank
      ≤ outerRankBound (poleBound n) (innerDegree n) p :=
  ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
    (rank_map_constantCoeff_outerCorrectionMatrix_le n)

/-- The rank of the conjugated correction `C^out 𝓛_p (C^out)ᵀ`, taken over `ℚ_p[X]`, is at most
`r_p`. -/
theorem rank_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_le_polynomial (n : ℕ) :
    (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        outerCorrectionMatrix p n *
        (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose).rank
      ≤ outerRankBound (poleBound n) (innerDegree n) p :=
  ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
    (rank_outerCorrectionMatrix_le n)

end Zeta5Irr
