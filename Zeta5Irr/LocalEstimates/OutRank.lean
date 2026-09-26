/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutLVanish
public import Zeta5Irr.LocalEstimates.Rp
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The rank of the correction matrix of the outer range

Let `p` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. The correction
matrix `𝓛_p = p (G_K - G_K^∘)` has rank at most `r_p = max(0, K + 4 N - 2 p + 2)` over `ℚ_p`.

Put `ρ = max(0, K - 6 N + 2 p - 2 - h)`. For `k < ρ` and every `l < h` one has
`k + l < K - 6 N + 2 p - 3`, so the `k`-th row of `𝓛_p` vanishes. Hence all nonzero rows lie
among the `h - ρ` indices `ρ ≤ k < h`, and the rank is at most `h - ρ`. With `K = 40 n`,
`N = 3 n` and `h = 37 n` one checks `h - ρ ≤ r_p`: if `ρ = 0` then `h ≤ K + 4 N - 2 p + 2`,
and otherwise `h - ρ = K + 4 N - 2 p + 2`.

## Main results

* `Zeta5Irr.rank_map_outerCorrectionMatrix_le`: for any map `f` from `ℚ_p[X]` to a commutative
  semiring with the strong rank condition sending `0` to `0`, the matrix `f(𝓛_p)` has rank at
  most `r_p`.
* `Zeta5Irr.rank_map_constantCoeff_outerCorrectionMatrix_le`: `rank_{ℚ_p} 𝓛_p ≤ r_p`, the
  entries of `𝓛_p` being read in `ℚ_p` through their constant coefficients.
* `Zeta5Irr.rank_outerCorrectionMatrix_le`: the rank of `𝓛_p` over `ℚ_p[X]` is at most `r_p`.

## Implementation notes

* `𝓛_p` is a matrix over `ℚ_p[X]` whose entries are constants
  (`Zeta5Irr.outerCorrectionMatrix_apply_eq_C`). Its rank over `ℚ_p` is the rank of the matrix
  of constant coefficients; the main statement is proved for the image of `𝓛_p` under any
  zero-preserving map, which covers both this and the rank over `ℚ_p[X]`.
* The source assumes `p ≥ 7`, `p ≤ K < 3 p`, `p ^ 2 > 2 K`, `2 N < p`, `5 N ≤ 2 p - 2` and
  `n > 0`. None of these is needed: the argument uses only the vanishing of the low rows and
  the identities `K = 40 n`, `N = 3 n`, `h = 37 n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **The rank of the correction.** For every map `f` from `ℚ_p[X]` to a commutative semiring
with the strong rank condition that sends `0` to `0`, the matrix obtained from `𝓛_p` by
applying `f` entrywise has rank at most `r_p`. -/
theorem rank_map_outerCorrectionMatrix_le {R : Type*} [CommSemiring R] [StrongRankCondition R]
    (n : ℕ) (f : ℚ_[p][X] → R) (hf : f 0 = 0) :
    ((outerCorrectionMatrix p n).map f).rank ≤
      outerRankBound (poleBound n) (innerDegree n) p := by
  classical
  set ρ := 2 * p - 2 - 15 * n with hρ
  have hp := (Fact.out : p.Prime).two_le
  have hrow : Function.support ((outerCorrectionMatrix p n).map f).row ⊆
      ({k | ρ ≤ (k : ℕ)} : Finset (Fin (matrixOrder n))) := by
    intro k hk
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    by_contra hkρ
    refine hk (funext fun l ↦ ?_)
    rw [Matrix.row_apply, Matrix.map_apply, outerCorrectionMatrix_apply_eq_zero, hf]
    · rfl
    have hl := l.isLt
    unfold poleBound innerDegree
    unfold matrixOrder at hl
    omega
  refine (Matrix.rank_le_card_of_support_subset _ _ hrow).trans ?_
  have hcard : #({k | ρ ≤ (k : ℕ)} : Finset (Fin (matrixOrder n))) ≤ matrixOrder n - ρ := by
    calc #({k | ρ ≤ (k : ℕ)} : Finset (Fin (matrixOrder n)))
        ≤ #(Ico ρ (matrixOrder n)) := by
          refine card_le_card_of_injOn (fun k ↦ (k : ℕ)) (fun k hk ↦ ?_)
            (fun a _ b _ h ↦ Fin.ext h)
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
          simp [hk, k.isLt]
      _ = matrixOrder n - ρ := Nat.card_Ico _ _
  refine hcard.trans ?_
  unfold outerRankBound matrixOrder poleBound innerDegree
  omega

/-- **The rank of the correction** (`rank_{ℚ_p} 𝓛_p ≤ r_p`). The entries of `𝓛_p` are
constants of `ℚ_p[X]`; read in `ℚ_p` through their constant coefficients, they form a matrix
over `ℚ_p` of rank at most `r_p = max(0, K + 4 N - 2 p + 2)`. -/
@[zeta5irr "lem_out_rank"]
theorem rank_map_constantCoeff_outerCorrectionMatrix_le (n : ℕ) :
    ((outerCorrectionMatrix p n).map constantCoeff).rank ≤
      outerRankBound (poleBound n) (innerDegree n) p :=
  rank_map_outerCorrectionMatrix_le n _ (map_zero _)

/-- The rank of `𝓛_p` over `ℚ_p[X]` is at most `r_p`. -/
theorem rank_outerCorrectionMatrix_le (n : ℕ) :
    (outerCorrectionMatrix p n).rank ≤ outerRankBound (poleBound n) (innerDegree n) p := by
  simpa using rank_map_outerCorrectionMatrix_le n id rfl

end Zeta5Irr
