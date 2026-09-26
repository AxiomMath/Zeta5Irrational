/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutGcirc
public import Zeta5Irr.LocalEstimates.OutV

/-!
# The outer range: the conjugated decomposition

Let `p` be an odd prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`, with
`p ≤ K`. Conjugating the Gram matrix `G_K^∘` of the integral part `Φ₀` of the outer form by the
outer coefficient matrix `C^out` computes `Φ₀` on the separating basis:
`(C^out G_K^∘ (C^out)ᵀ)_{(a,i),(c,j)} = Φ₀(P_a q_{a,i}, P_c q_{c,j})`.

The point is that every basis polynomial `P_a q_{a,i}` has degree `< K - N = h`, so that the
row `(a, i)` of `C^out` is its full coefficient vector; the identity is then bilinearity of `Φ₀`.

## Main results

* `Zeta5Irr.natDegree_complClassFactor_mul_outerLocalPoly_lt`: for `p` odd, `p ≤ K`,
  `0 ≤ a ≤ m°` and `i < deg Q_a`, `deg (P_a q_{a,i}) < K - N`.
* `Zeta5Irr.outerCoeffMatrix_mul_outerIntegralGramMatrix_mul_transpose_apply`:
  `(C^out G_K^∘ (C^out)ᵀ)_{(a,i),(c,j)} = Φ₀(P_a q_{a,i}, P_c q_{c,j})`.

## Implementation notes

* The matrix `C^out` is taken with entries in `ℚ_p[X]`, the ring of `G_K^∘`; by
  `Zeta5Irr.map_outerCoeffMatrix` it is the image of the rational matrix, whose rows are the
  coefficient vectors of the rational polynomials `P_a q_{a,i}` on which `Φ₀` is evaluated.
* Of the source's hypotheses on `p` and `K` only `p` odd and `p ≤ K` are used: they give
  `deg q_{a,i} = i` for `a ≥ 1`. The remaining ones (`K ∈ 40 ℤ_{>0}`, `p ≥ 7`, `K < 3 p`,
  `p² > 2 K`, `2 N < p`, `5 N ≤ 2 p - 2`) are not needed for this identity.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.12: the outer range, the conjugated decomposition.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- For `p` odd with `p ≤ K`, `0 ≤ a ≤ m°` and `i < deg Q_a`, the separating basis polynomial
`P_a q_{a,i}` has degree `< K - N`. -/
theorem natDegree_complClassFactor_mul_outerLocalPoly_lt {R : Type*} [CommRing R]
    [Nontrivial R] {p N K : ℕ} (hp : Odd p) (hK : p ≤ K) {a : ℕ} (ha : a ≤ mStar p) {i : ℕ}
    (hi : i < #(residuePoleIndices p (a : ℤ) N K)) :
    (complClassFactor R p (a : ℤ) N K * outerLocalPoly R p K (a : ℤ) i).natDegree < K - N := by
  have hq : (outerLocalPoly R p K (a : ℤ) i).natDegree = i := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · simpa using natDegree_multiplePoleProduct (R := R) p i
    · rw [outerLocalPoly_of_ne_zero (by omega)]
      exact natDegree_outerBasis hp (by omega) (by exact_mod_cast ha) hK i
  exact natDegree_complClassFactor_mul_lt (outerLocalPoly_monic p K _ i) (by rwa [hq])

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The conjugated decomposition of the outer range: for `p` odd with `p ≤ K`, and for index
pairs `(a, i)`, `(c, j)` with `0 ≤ a, c ≤ m°`, `i < deg Q_a` and `j < deg Q_c`,
`(C^out G_K^∘ (C^out)ᵀ)_{(a,i),(c,j)} = Φ₀(P_a q_{a,i}, P_c q_{c,j})`. -/
@[zeta5irr "lem_out_conj_entry"]
theorem outerCoeffMatrix_mul_outerIntegralGramMatrix_mul_transpose_apply (hp : p ≠ 2)
    (hK : p ≤ poleBound n)
    (ai cj : Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) :
    (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        outerIntegralGramMatrix p n *
        (outerCoeffMatrix ℚ_[p][X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose)
        ai cj =
      outerIntegralForm p n
        (complClassFactor ℚ p (ai.1 : ℕ) (innerDegree n) (poleBound n) *
          outerLocalPoly ℚ p (poleBound n) (ai.1 : ℕ) ai.2)
        (complClassFactor ℚ p (cj.1 : ℕ) (innerDegree n) (poleBound n) *
          outerLocalPoly ℚ p (poleBound n) (cj.1 : ℕ) cj.2) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hh : poleBound n - innerDegree n = matrixOrder n := by
    simp only [poleBound, innerDegree, matrixOrder]; omega
  have hdeg (bk : Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) :
      (complClassFactor ℚ p (bk.1 : ℕ) (innerDegree n) (poleBound n) *
        outerLocalPoly ℚ p (poleBound n) (bk.1 : ℕ) bk.2).natDegree < matrixOrder n :=
    hh ▸ natDegree_complClassFactor_mul_outerLocalPoly_lt hodd hK
      (Nat.lt_succ_iff.mp bk.1.2) bk.2.2
  rw [← sum_outerCoeffMatrix_mul_X_pow ai (hdeg ai),
    ← sum_outerCoeffMatrix_mul_X_pow cj (hdeg cj),
    ← map_outerCoeffMatrix (algebraMap ℚ ℚ_[p][X])]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    outerIntegralGramMatrix_apply, outerIntegralForm_sum_left, outerIntegralForm_sum_right,
    Finset.sum_mul]
  simp_rw [← smul_eq_C_mul, outerIntegralForm_smul_left, outerIntegralForm_smul_right,
    Algebra.smul_def]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

end Zeta5Irr
