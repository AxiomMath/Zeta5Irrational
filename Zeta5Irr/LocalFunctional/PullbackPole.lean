/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauXDecomp
public import Zeta5Irr.LocalFunctional.TauMonomial
public import Zeta5Irr.Parameters.PoleValue

/-!
# The pullback identity at a simple pole

For `j ≥ 1` the value of the functional `τ_X` on `-x ^ 5` with poles `R = {j, -j}` is the pole
value `ν_j(X) = j ^ 4 (X - H_j^{(5)}) - 1/4 + 1/(2j)`. This is the pullback of the simple pole
`1 / (t + j ^ 2)` under `t = -x ^ 2`: here `E_R = x ^ 2 - j ^ 2`, and
`-x ^ 5 = (-x ^ 3 - j ^ 2 x) E_R - (j ^ 4 / 2)(x + j) - (j ^ 4 / 2)(x - j)`,
so that `τ_X(-x ^ 5; R) = -κ_3 - j ^ 2 κ_1 - (j ^ 4 / 2)(H_j^{(5)} + H_{j-1}^{(5)} - 2X)`.

## Main results

* `Zeta5Irr.tauX_neg_X_pow_five_pair`: `τ_X(-x ^ 5; {j, -j}) = ν_j(X)` for `j ≥ 1`.

## Implementation notes

The index `j` is a natural number with `j ≠ 0`, matching `Zeta5Irr.poleValue`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.3 (the pullback identity).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C)

/-- For `j ≥ 1`, `τ_X(-x ^ 5; {j, -j}) = ν_j(X)`. -/
@[zeta5irr "lem_pullback_pole"]
theorem tauX_neg_X_pow_five_pair {j : ℕ} (hj : j ≠ 0) :
    tauX {(j : ℤ), -(j : ℤ)} (-X ^ 5) = poleValue j := by
  have hne : (j : ℤ) ≠ -(j : ℤ) := by omega
  have hE : intPoleProduct {(j : ℤ), -(j : ℤ)} ℚ = (X - C (j : ℚ)) * (X + C (j : ℚ)) := by
    rw [intPoleProduct_insert _ (by simpa using hne), intPoleProduct_singleton]
    simp [sub_eq_add_neg]
  have h1 : ({(j : ℤ), -(j : ℤ)} : Finset ℤ).erase (j : ℤ) = {-(j : ℤ)} :=
    Finset.erase_insert (by simpa using hne)
  have h2 : ({(j : ℤ), -(j : ℤ)} : Finset ℤ).erase (-(j : ℤ)) = {(j : ℤ)} := by
    rw [Finset.erase_insert_of_ne hne, Finset.erase_singleton, insert_empty_eq]
  rw [tauX_eq_of_eq_mul_add_sum (P := -X ^ 3 - C ((j : ℚ) ^ 2) * X)
    (fun _ ↦ -((j : ℚ) ^ 4 / 2))]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hr : reflectIndex (-((k + 1 : ℕ) : ℤ)) = k := rfl
    rw [Finset.sum_pair hne, map_sub, map_neg, tau_X_pow_eq_kappa,
      ← pow_one (X : ℚ[X]), tau_C_mul_X_pow, kappa_add_three 0, reflectIndex_natCast, hr]
    refine Polynomial.funext fun x ↦ ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, eval_poleValue]
    rw [harmonicFive_succ]
    norm_num
    field_simp
    ring
  · rw [Finset.sum_pair hne, hE, h1, h2, intPoleProduct_singleton, intPoleProduct_singleton]
    refine Polynomial.funext fun x ↦ ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_neg, Int.cast_neg, Int.cast_natCast]
    ring

end Zeta5Irr
