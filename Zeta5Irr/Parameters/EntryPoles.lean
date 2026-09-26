/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramMatrix
public import Zeta5Irr.Parameters.MuXCancel

/-!
# The poles of the entries of `G_K(X)`

Let `K = 40 n`, `N = 3 n` and `h = 37 n`. The entries of the matrix `G_K(X)` are
`μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K})`. Since `D_N` is divisible by `t + j ^ 2` for every
`1 ≤ j ≤ N`, one factor of `D_N` cancels the poles at `-1, -4, …, -N ^ 2`, so that
`μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K}) = μ_X(D_N(t) ^ 5 t ^ (i + j); {N + 1, …, K})`.

More generally, for finite sets `T ⊆ S` of natural numbers and any `B ∈ ℚ[t]`,
`μ_X(D_T B; S) = μ_X(B; S \ T)`: this is the cancellation of one pole, applied once for each
element of `T`.

## Main results

* `Zeta5Irr.rationalFunctional_poleProduct_mul`: `μ_X(D_T B; S) = μ_X(B; S \ T)` for `T ⊆ S`.
* `Zeta5Irr.rationalFunctional_poleProductRange_mul`:
  `μ_X(D_N B; {1, …, K}) = μ_X(B; {N + 1, …, K})` for `N ≤ K`.
* `Zeta5Irr.rationalFunctional_poleProductRange_pow_six_mul_X_pow`:
  `μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K}) = μ_X(D_N(t) ^ 5 t ^ (i + j); {N + 1, …, K})`.
* `Zeta5Irr.gramMatrix_apply_eq`: the same identity for the entries of `G_K(X)`.

## Implementation notes

* The source states the identity for `0 ≤ i, j < h`; the bound on `i` and `j` is not used,
  and `Zeta5Irr.rationalFunctional_poleProductRange_pow_six_mul_X_pow` is stated for all
  natural numbers `i` and `j`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- For `T ⊆ S`, `μ_X(D_T B; S) = μ_X(B; S \ T)`: the factor `D_T` cancels the poles of
`D_T B / D_S` at `-j ^ 2` for `j ∈ T`. -/
theorem rationalFunctional_poleProduct_mul {S T : Finset ℕ} (h : T ⊆ S) (B : ℚ[X]) :
    rationalFunctional S (poleProduct T ℚ * B) = rationalFunctional (S \ T) B := by
  induction T using Finset.induction_on generalizing S with
  | empty => simp [poleProduct_empty]
  | insert a T ha ih =>
    have haS : a ∈ S := h (mem_insert_self a T)
    have hT : T ⊆ S.erase a := fun x hx ↦
      mem_erase.2 ⟨fun hxa ↦ ha (hxa ▸ hx), h (mem_insert_of_mem hx)⟩
    rw [poleProduct_insert _ ha, mul_assoc, rationalFunctional_X_add_C_mul haS, ih hT,
      sdiff_insert, erase_sdiff_comm]

/-- For `N ≤ K`, `μ_X(D_N B; {1, …, K}) = μ_X(B; {N + 1, …, K})`. -/
theorem rationalFunctional_poleProductRange_mul {N K : ℕ} (h : N ≤ K) (B : ℚ[X]) :
    rationalFunctional (Icc 1 K) (poleProductRange N ℚ * B) =
      rationalFunctional (Icc (N + 1) K) B := by
  have hS : Icc 1 K \ Icc 1 N = Icc (N + 1) K := by
    ext x
    simp only [mem_sdiff, mem_Icc]
    omega
  rw [poleProductRange, rationalFunctional_poleProduct_mul (Icc_subset_Icc_right h), hS]

/-- The poles of the entries of `G_K(X)`: with `K = 40 n` and `N = 3 n`,
`μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K}) = μ_X(D_N(t) ^ 5 t ^ (i + j); {N + 1, …, K})`. -/
@[zeta5irr "lem_entry_poles"]
theorem rationalFunctional_poleProductRange_pow_six_mul_X_pow (n i j : ℕ) :
    rationalFunctional (Icc 1 (poleBound n))
        (poleProductRange (innerDegree n) ℚ ^ 6 * X ^ (i + j)) =
      rationalFunctional (Icc (innerDegree n + 1) (poleBound n))
        (poleProductRange (innerDegree n) ℚ ^ 5 * X ^ (i + j)) := by
  rw [pow_succ', mul_assoc, rationalFunctional_poleProductRange_mul]
  simp only [innerDegree, poleBound]
  omega

/-- The entries of `G_K(X)`: `G_K(X)_{ij} = μ_X(D_N(t) ^ 5 t ^ (i + j); {N + 1, …, K})`. -/
theorem gramMatrix_apply_eq (n : ℕ) (i j : Fin (matrixOrder n)) :
    gramMatrix n i j = rationalFunctional (Icc (innerDegree n + 1) (poleBound n))
      (poleProductRange (innerDegree n) ℚ ^ 5 * X ^ ((i : ℕ) + j)) := by
  rw [gramMatrix_apply, rationalFunctional_poleProductRange_pow_six_mul_X_pow]

end Zeta5Irr
