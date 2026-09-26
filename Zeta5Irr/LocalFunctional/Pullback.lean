/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MuX
public import Zeta5Irr.LocalFunctional.TauPf
public import Zeta5Irr.LocalFunctional.TauXCancel
public import Zeta5Irr.LocalFunctional.PullbackPoly
public import Zeta5Irr.LocalFunctional.PullbackPole

/-!
# The pullback identity

Let `S` be a finite set of positive integers and `R = S ∪ (-S) ⊆ ℤ`. The rational functional
`μ_X(·; S)` on `ℚ[t]` is the pullback of the functional `τ_X(·; R)` on `ℚ[x]` along the
substitution `t = -x ^ 2`, twisted by `(-1) ^ #S x ^ 5`:
`μ_X(A; S) = τ_X((-1) ^ #S x ^ 5 A(-x ^ 2); S ∪ (-S))` for every `A ∈ ℚ[t]`.

Under `t = -x ^ 2` the pole product becomes `D_S(-x ^ 2) = ∏_{j ∈ S} (j ^ 2 - x ^ 2)
= (-1) ^ #S E_R(x)`. Writing `A = P D_S + ∑_{j ∈ S} c_j D_{S \ {j}}` (partial fractions,
`c_j = A(-j ^ 2) / D_S'(-j ^ 2)`) and substituting, the polynomial part pulls back to
`x ^ 5 P(-x ^ 2) E_R`, whose `τ_X` is `τ(x ^ 5 P(-x ^ 2)) = μ(P)`, and the `j`-th simple
fraction pulls back to `-x ^ 5 E_{R \ {j, -j}}`, whose `τ_X` is `τ_X(-x ^ 5; {j, -j}) = ν_j(X)`.
Both reductions cancel the common factors `x - r` one at a time.

## Main results

* `Zeta5Irr.rationalFunctional_eq_tauX`: the pullback identity
  `μ_X(A; S) = τ_X((-1) ^ #S x ^ 5 A(-x ^ 2); S ∪ (-S))`.
* `Zeta5Irr.tauX_union_intPoleProduct_mul`: for disjoint `T`, `U`,
  `τ_X(E_U Q; T ∪ U) = τ_X(Q; T)`.
* `Zeta5Irr.poleProduct_comp_neg_X_sq`: `D_S(-x ^ 2) = (-1) ^ #S E_{S ∪ (-S)}(x)` when `0 ∉ S`.

## Implementation notes

The set `S` is a `Finset ℕ` with the hypothesis `0 ∉ S`, and `S ∪ (-S)` is the `Finset ℤ`
`S.image (↑) ∪ S.image (-↑)`. The hypothesis `0 ∉ S` makes this union disjoint, of size `2 #S`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.3 (the pullback identity).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

/-- Cancelling a block of poles: if `T` and `U` are disjoint then
`τ_X(E_U Q; T ∪ U) = τ_X(Q; T)`. -/
theorem tauX_union_intPoleProduct_mul {T U : Finset ℤ} (h : Disjoint T U) (Q : ℚ[X]) :
    tauX (T ∪ U) (intPoleProduct U ℚ * Q) = tauX T Q := by
  induction U using Finset.induction_on generalizing Q with
  | empty => rw [union_empty, intPoleProduct_empty, one_mul]
  | insert u U hu ih =>
    have huT : u ∉ T := fun h' ↦ disjoint_left.1 h h' (mem_insert_self u U)
    have hTU : Disjoint T U := h.mono_right (subset_insert u U)
    have hmem : u ∈ T ∪ insert u U := mem_union_right _ (mem_insert_self u U)
    have herase : (T ∪ insert u U).erase u = T ∪ U := by
      ext x
      simp only [mem_erase, mem_union, mem_insert]
      grind
    rw [intPoleProduct_insert _ hu, mul_assoc, tauX_X_sub_C_mul hmem, herase, ih hTU]

/-- For `0 ∉ T`, the pole polynomial of `T ∪ (-T)` is `∏_{j ∈ T} (x - j)(x + j)`. -/
theorem intPoleProduct_image_union_image_neg {T : Finset ℕ} (hT : 0 ∉ T) :
    intPoleProduct (T.image (fun j : ℕ ↦ (j : ℤ)) ∪ T.image (fun j : ℕ ↦ -(j : ℤ))) ℚ =
      ∏ j ∈ T, ((X - C (j : ℚ)) * (X + C (j : ℚ))) := by
  have hdisj : Disjoint (T.image (fun j : ℕ ↦ (j : ℤ))) (T.image (fun j : ℕ ↦ -(j : ℤ))) := by
    rw [disjoint_left]
    simp only [mem_image, not_exists, not_and]
    rintro _ ⟨a, ha, rfl⟩ b hb hab
    have : a = 0 := by omega
    exact hT (this ▸ ha)
  rw [intPoleProduct, prod_union hdisj, prod_image (fun a _ b _ h ↦ by exact_mod_cast h),
    prod_image (fun a _ b _ h ↦ by simpa using h), ← prod_mul_distrib]
  refine prod_congr rfl fun j _ ↦ ?_
  simp [sub_eq_add_neg]

/-- For `0 ∉ T`, `D_T(-x ^ 2) = (-1) ^ #T E_{T ∪ (-T)}(x)`. -/
theorem poleProduct_comp_neg_X_sq {T : Finset ℕ} (hT : 0 ∉ T) :
    (poleProduct T ℚ).comp (-X ^ 2) = C ((-1) ^ #T) *
      intPoleProduct (T.image (fun j : ℕ ↦ (j : ℤ)) ∪ T.image (fun j : ℕ ↦ -(j : ℤ))) ℚ := by
  rw [intPoleProduct_image_union_image_neg hT, poleProduct, Polynomial.prod_comp, C_pow,
    ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ ↦ ?_
  simp only [add_comp, X_comp, C_comp, map_neg, map_one]
  rw [C_pow]
  ring

/-- **The pullback identity.** For a finite set `S` of positive integers and `A ∈ ℚ[t]`,
`μ_X(A; S) = τ_X((-1) ^ #S x ^ 5 A(-x ^ 2); S ∪ (-S))`. -/
@[zeta5irr "lem_pullback"]
theorem rationalFunctional_eq_tauX {S : Finset ℕ} (hS : 0 ∉ S) (A : ℚ[X]) :
    rationalFunctional S A =
      tauX (S.image (fun j : ℕ ↦ (j : ℤ)) ∪ S.image (fun j : ℕ ↦ -(j : ℤ)))
        (C ((-1) ^ #S) * X ^ 5 * A.comp (-X ^ 2)) := by
  set R := S.image (fun j : ℕ ↦ (j : ℤ)) ∪ S.image (fun j : ℕ ↦ -(j : ℤ)) with hR
  have hprod : ∀ s : Finset ℕ, ∏ j ∈ s, (X - C (-(j : ℚ) ^ 2)) = poleProduct s ℚ := fun s ↦ by
    simp [poleProduct, sub_eq_add_neg]
  have hinj : Set.InjOn (fun j : ℕ ↦ -(j : ℚ) ^ 2) S := fun a _ b _ h ↦
    Nat.pow_left_injective two_ne_zero (by exact_mod_cast neg_inj.1 h)
  have hpf := eq_mul_prod_add_sum_eval_div_derivative hinj
    (A := A) (P := A /ₘ poleProduct S ℚ) (B := A %ₘ poleProduct S ℚ)
    (by rw [hprod, mul_comm, add_comm]; exact (modByMonic_add_div A _).symm)
    (by rw [← degree_poleProduct S ℚ]; exact degree_modByMonic_lt A (monic_poleProduct S ℚ))
  simp only [hprod] at hpf
  have hadd : ∀ (s : Finset ℕ) (f : ℕ → ℚ[X]),
      tauX R (∑ i ∈ s, f i) = ∑ i ∈ s, tauX R (f i) :=
    fun s f ↦ map_sum (AddMonoidHom.mk' (tauX R) (tauX_add R)) f s
  rw [rationalFunctional_apply]
  conv_rhs => rw [hpf]
  rw [add_comp, mul_add, tauX_add, Polynomial.sum_comp, Finset.mul_sum, hadd]
  congr 1
  · rw [mul_comp, poleProduct_comp_neg_X_sq hS, ← hR,
      show C ((-1 : ℚ) ^ #S) * X ^ 5 * ((A /ₘ poleProduct S ℚ).comp (-X ^ 2) *
        (C ((-1) ^ #S) * intPoleProduct R ℚ)) = C ((-1) ^ #S * (-1) ^ #S) *
        (intPoleProduct R ℚ * (X ^ 5 * (A /ₘ poleProduct S ℚ).comp (-X ^ 2))) by
        rw [C_mul]; ring,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1, one_mul, momentFunctional_eq_tau_pullback]
    have h := tauX_union_intPoleProduct_mul (disjoint_empty_left R)
      (X ^ 5 * (A /ₘ poleProduct S ℚ).comp (-X ^ 2))
    rw [empty_union] at h
    rw [h]
    simp [tauX]
  · refine sum_congr rfl fun i hi ↦ ?_
    have hi0 : i ≠ 0 := fun h ↦ hS (h ▸ hi)
    have hS' : 0 ∉ S.erase i := fun h ↦ hS (mem_of_mem_erase h)
    set R' := (S.erase i).image (fun j : ℕ ↦ (j : ℤ)) ∪ (S.erase i).image (fun j : ℕ ↦ -(j : ℤ))
      with hR'
    have hRi : R = {(i : ℤ), -(i : ℤ)} ∪ R' := by
      ext x
      simp only [hR, hR', mem_union, mem_image, mem_erase, mem_insert, mem_singleton]
      grind
    have hdisj : Disjoint ({(i : ℤ), -(i : ℤ)} : Finset ℤ) R' := by
      simp only [hR', disjoint_left, mem_insert, mem_singleton, mem_union, mem_image, mem_erase]
      grind
    have hcard : #S = #(S.erase i) + 1 := (card_erase_add_one hi).symm
    rw [mul_comp, C_comp, poleProduct_comp_neg_X_sq hS', ← hR',
      show C ((-1 : ℚ) ^ #S) * X ^ 5 * (C (A.eval (-(i : ℚ) ^ 2) /
          (derivative (poleProduct S ℚ)).eval (-(i : ℚ) ^ 2)) *
        (C ((-1) ^ #(S.erase i)) * intPoleProduct R' ℚ)) =
        (A.eval (-(i : ℚ) ^ 2) / (derivative (poleProduct S ℚ)).eval (-(i : ℚ) ^ 2)) •
        (C ((-1) ^ #(S.erase i) * (-1) ^ #(S.erase i)) * (intPoleProduct R' ℚ * -X ^ 5)) by
        rw [smul_eq_C_mul, hcard, pow_succ, C_mul, C_mul, C_neg, C_1]; ring,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, C_1, one_mul, tauX_smul, hRi,
      tauX_union_intPoleProduct_mul hdisj, tauX_neg_X_pow_five_pair hi0, smul_eq_C_mul]

end Zeta5Irr
