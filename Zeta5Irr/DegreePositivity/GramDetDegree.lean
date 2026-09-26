/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramDeterminant
public import Zeta5Irr.DegreePositivity.TopCoeff
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The degree of `Δ_K`

Let `K = 40 n`, `N = 3 n` and `h = 37 n`. The determinant `Δ_K = det G_K(X)` has degree
exactly `h`.

Every entry of the `h × h` matrix `G_K(X)` has degree at most one in `X`, so `Δ_K` has degree
at most `h`. The coefficient of `X ^ h` in `Δ_K` is
`(-1) ^ (h (h - 1) / 2) ∏_{r = N + 1}^{K} r ^ 4 D_N(-r ^ 2) ^ 5`, and each factor is nonzero:
for `N < r` and `1 ≤ j ≤ N` we have `j ^ 2 < r ^ 2`, so
`D_N(-r ^ 2) = ∏_{j = 1}^{N} (j ^ 2 - r ^ 2) ≠ 0`.

## Main results

* `Zeta5Irr.natDegree_det_le_of_natDegree_le_one`: a square polynomial matrix whose entries
  have degree at most one has determinant of degree at most its size.
* `Zeta5Irr.coeff_gramDet_matrixOrder_ne_zero`: the coefficient of `X ^ h` in `Δ_K` is nonzero.
* `Zeta5Irr.natDegree_gramDet`, `Zeta5Irr.degree_gramDet`: `Δ_K` has degree exactly `h`.

## Implementation notes

* The statements hold for every `n`, including `n = 0`, where `Δ_K = 1` and `h = 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the degree of the determinant).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- If every entry of a square polynomial matrix `M` has degree at most one, then `det M` has
degree at most the size of `M`. -/
theorem natDegree_det_le_of_natDegree_le_one {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (M : Matrix n n R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    M.det.natDegree ≤ Fintype.card n := by
  rw [eq_X_smul_map_C_add_map_C_of_natDegree_le_one M hM]
  exact natDegree_det_X_add_C_le _ _

/-- `Δ_K` has degree at most `h`. -/
theorem natDegree_gramDet_le (n : ℕ) : (gramDet n).natDegree ≤ matrixOrder n := by
  simpa [gramDet] using natDegree_det_le_of_natDegree_le_one (gramMatrix n)
    fun i j ↦ by rw [gramMatrix_apply]; exact natDegree_rationalFunctional_le _ _

/-- The coefficient of `X ^ h` in `Δ_K` is nonzero. -/
theorem coeff_gramDet_matrixOrder_ne_zero (n : ℕ) :
    (gramDet n).coeff (matrixOrder n) ≠ 0 := by
  rw [coeff_gramDet_matrixOrder]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
  refine prod_ne_zero_iff.mpr fun r hr ↦ ?_
  obtain ⟨hr1, -⟩ := mem_Icc.mp hr
  refine mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))) (pow_ne_zero _ ?_)
  rw [eval_poleProductRange]
  refine prod_ne_zero_iff.mpr fun j hj ↦ ?_
  obtain ⟨-, hj⟩ := mem_Icc.mp hj
  have hjr : (j : ℚ) ^ 2 < (r : ℚ) ^ 2 := by
    gcongr
    exact_mod_cast (by omega : j < r)
  linarith

/-- **The degree of `Δ_K`.** With `K = 40 n` and `h = 37 n`, `Δ_K` has degree exactly `h`,
stated for `natDegree`. -/
@[zeta5irr "lem_deg_DeltaK"]
theorem natDegree_gramDet (n : ℕ) : (gramDet n).natDegree = matrixOrder n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_gramDet_le n)
    (coeff_gramDet_matrixOrder_ne_zero n)

/-- **The degree of `Δ_K`.** With `K = 40 n` and `h = 37 n`, `Δ_K` has degree exactly `h`. -/
@[zeta5irr "lem_deg_DeltaK"]
theorem degree_gramDet (n : ℕ) : (gramDet n).degree = matrixOrder n := by
  have h0 : gramDet n ≠ 0 := fun h ↦ coeff_gramDet_matrixOrder_ne_zero n (by simp [h])
  rw [degree_eq_natDegree h0, natDegree_gramDet]

end Zeta5Irr
