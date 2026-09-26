/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutLInt
public import Zeta5Irr.LocalEstimates.OutV

/-!
# The outer range: the conjugated correction is integral

Let `p ≥ 7` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. Conjugating
the correction matrix `𝓛_p = p (G_K - G_K^∘)` by the outer coefficient matrix `C^out` gives a
matrix `C^out 𝓛_p (C^out)ᵀ` whose entries are all constant `p`-adic integers. Indeed, the
entries of `C^out` are integers and those of `𝓛_p` are constant `p`-adic integers, and each
entry of the triple product is a finite sum of products of three such entries.

## Main results

* `Zeta5Irr.exists_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_apply_eq_C`:
  every entry of `C^out 𝓛_p (C^out)ᵀ` is a constant `p`-adic integer.

## Implementation notes

* The matrices have entries in `ℚ_p[X]`, the ring of `𝓛_p`; an entry "lies in `ℤ_p`" when it
  is the constant polynomial `C z` for some `z ∈ ℤ_p`, as in
  `Zeta5Irr.exists_outerCorrectionMatrix_apply_eq_C_padicInt`.
* The source assumes `K ∈ 40 ℤ_{>0}`, `p ≥ 7`, `p ≤ K < 3 p`, `p² > 2 K`, `2 N < p` and
  `5 N ≤ 2 p - 2`. Only `p ≥ 5` is used (through the integrality of `𝓛_p`), and the row
  parameters `N`, `K` of `C^out` are arbitrary; the source's case is `N = 3 n`, `K = 40 n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.12 (The outer range: the conjugated decomposition).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **The conjugated correction is integral** (§5.12). For a prime `p ≥ 5` (in the source,
`p ≥ 7` with further conditions on `p`, `N` and `K`), every entry of `C^out 𝓛_p (C^out)ᵀ` is a
constant `p`-adic integer. -/
@[zeta5irr "lem_out_conj_int"]
theorem exists_outerCoeffMatrix_mul_outerCorrectionMatrix_mul_transpose_apply_eq_C
    (hp : 5 ≤ p) (n N K : ℕ)
    (ai cj : Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) :
    ∃ z : ℤ_[p],
      (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n) * outerCorrectionMatrix p n *
        (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n)).transpose) ai cj = C (z : ℚ_[p]) := by
  let f : ℤ_[p] →+* ℚ_[p][X] := C.comp PadicInt.Coe.ringHom
  have hC (x y) : outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n) x y ∈ f.range := by
    rw [← map_intCast_outerCoeffMatrix]
    exact ⟨(outerCoeffMatrix ℤ p N K (matrixOrder n) x y : ℤ_[p]), by simp [f]⟩
  have hL (k l) : outerCorrectionMatrix p n k l ∈ f.range := by
    obtain ⟨z, hz⟩ := exists_outerCorrectionMatrix_apply_eq_C_padicInt hp n k l
    exact ⟨z, hz.symm⟩
  obtain ⟨z, hz⟩ : (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n) *
      outerCorrectionMatrix p n *
      (outerCoeffMatrix ℚ_[p][X] p N K (matrixOrder n)).transpose) ai cj ∈ f.range := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Subring.sum_mem _ fun _ _ ↦ Subring.mul_mem _
      (Subring.sum_mem _ fun _ _ ↦ Subring.mul_mem _ (hC _ _) (hL _ _)) (hC _ _)
  exact ⟨z, hz.symm⟩

end Zeta5Irr
