/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.DetSign
public import Zeta5Irr.Parameters.MuX

/-!
# Cancelling a pole of the rational functional

Let `S` be a finite set of positive integers, `j₀ ∈ S`, and let `A ∈ ℚ[t]` be divisible by
`t + j₀ ^ 2`, say `A = (t + j₀ ^ 2) A₁`. Then `μ_X(A; S) = μ_X(A₁; S \ {j₀})`: the factor
`t + j₀ ^ 2` of `A` cancels the pole of `A / D_S` at `-j₀ ^ 2`, and the functional sees only
the rational function `A / D_S = A₁ / D_{S \ {j₀}}`.

The proof compares the two sides term by term. Since `D_S = (t + j₀ ^ 2) D_{S \ {j₀}}`, a
division `A₁ = P D_{S \ {j₀}} + B₁` gives the division `A = P D_S + (t + j₀ ^ 2) B₁`, so both
sides have the same polynomial part `μ(P)`. The residue term at `j₀` vanishes because
`A(-j₀ ^ 2) = 0`; for `j ≠ j₀` both `A(-j ^ 2)` and `D_S'(-j ^ 2)` carry the extra nonzero
factor `j₀ ^ 2 - j ^ 2`, which cancels.

## Main results

* `Zeta5Irr.rationalFunctional_X_add_C_mul`:
  `μ_X((t + j₀ ^ 2) A₁; S) = μ_X(A₁; S \ {j₀})` for `j₀ ∈ S`.

## Implementation notes

* The hypothesis "`A` is divisible by `t + j₀ ^ 2`" and the quotient `A / (t + j₀ ^ 2)` are
  expressed by writing `A = (t + j₀ ^ 2) A₁` with `A₁` explicit.
* The source takes `S ⊂ ℤ_{>0}`; here `S : Finset ℕ` with no positivity hypothesis. The
  cancelled factors `j₀ ^ 2 - j ^ 2` are nonzero for distinct natural numbers `j`, `j₀`,
  since squaring is injective on `ℕ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- If `A = (t + j₀ ^ 2) A₁` with `j₀ ∈ S`, then `μ_X(A; S) = μ_X(A₁; S \ {j₀})`: the factor
`t + j₀ ^ 2` cancels the pole of `A / D_S` at `-j₀ ^ 2`. -/
@[zeta5irr "lem_muX_cancel"]
theorem rationalFunctional_X_add_C_mul {S : Finset ℕ} {j₀ : ℕ} (h : j₀ ∈ S) (A₁ : ℚ[X]) :
    rationalFunctional S ((X + C ((j₀ : ℚ) ^ 2)) * A₁) = rationalFunctional (S.erase j₀) A₁ := by
  set S₁ := S.erase j₀
  have hS : S = insert j₀ S₁ := (insert_erase h).symm
  have hj₀ : j₀ ∉ S₁ := notMem_erase j₀ S
  have hD : poleProduct S ℚ = (X + C ((j₀ : ℚ) ^ 2)) * poleProduct S₁ ℚ := by
    rw [hS, poleProduct_insert _ hj₀]
  set P := A₁ /ₘ poleProduct S₁ ℚ
  set B := A₁ %ₘ poleProduct S₁ ℚ
  have hA₁ : A₁ = P * poleProduct S₁ ℚ + B := by
    rw [mul_comm, add_comm]
    exact (modByMonic_add_div A₁ _).symm
  have hB : B.degree < (poleProduct S₁ ℚ).degree :=
    degree_modByMonic_lt _ (monic_poleProduct S₁ ℚ)
  have hB' : ((X + C ((j₀ : ℚ) ^ 2)) * B).degree < (poleProduct S ℚ).degree := by
    rw [hD, degree_mul, degree_mul, degree_X_add_C]
    exact WithBot.add_lt_add_left WithBot.one_ne_bot hB
  rw [rationalFunctional_eq_of_eq_mul_add (P := P) (B := (X + C ((j₀ : ℚ) ^ 2)) * B)
    (by rw [hD, hA₁]; ring) hB', rationalFunctional_apply]
  congr 1
  rw [hS, sum_insert hj₀]
  simp only [eval_mul, eval_add, eval_X, eval_C, neg_add_cancel, zero_mul, zero_div, C_0,
    zero_mul, zero_add]
  refine sum_congr rfl fun j hj ↦ ?_
  have hjj₀ : j ≠ j₀ := ne_of_mem_erase hj
  have hne : (j₀ : ℚ) ^ 2 - j ^ 2 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (Nat.pow_left_injective two_ne_zero).ne hjj₀.symm
  rw [← hS, eval_derivative_poleProduct_neg_sq (hS ▸ mem_insert_of_mem hj),
    eval_derivative_poleProduct_neg_sq hj]
  have hE : S.erase j = insert j₀ (S₁.erase j) := by
    rw [hS, erase_insert_of_ne hjj₀.symm]
  rw [hE, prod_insert (fun h' ↦ hj₀ (mem_of_mem_erase h')), ← neg_add_eq_sub,
    add_comm, mul_div_mul_left _ _ (by rwa [add_comm, neg_add_eq_sub])]

end Zeta5Irr
