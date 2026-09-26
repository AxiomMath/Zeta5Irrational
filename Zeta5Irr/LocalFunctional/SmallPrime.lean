/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG
public import Zeta5Irr.LocalFunctional.TauX
public import Zeta5Irr.LocalFunctional.QRK
public import Zeta5Irr.LocalFunctional.LocalVpGAdd
public import Zeta5Irr.LocalFunctional.SmallTau
public import Zeta5Irr.LocalFunctional.SmallPolyVal
public import Zeta5Irr.LocalFunctional.SmallHarmVal

/-!
# The Gauss valuation of `τ_X((K!)² A; R_K)` at a prime

Let `p` be a prime, `K, d ∈ ℕ`, and let `A ∈ ℚ[x]` have degree at most `d` and take integer
values at the integers. Then
`v_p^G(τ_X((K!)² A; R_K)) ≥ -6 ⌊log_p max(2K, d + 1)⌋ - v_p(24)`.

Write `Λ = ⌊log_p max(2K, d + 1)⌋`, `L₀ = ⌊log_p(2K)⌋` and
`M₀ = max(L₀, ⌊log_p max(1, d)⌋)`, so that `L₀, M₀, ⌊log_p(d + 1)⌋ ≤ Λ`. Since `A(ℤ_p) ⊆ ℤ_p`,
the quotient `P` of `(K!)² A` by `E_{R_K}` satisfies `P(ℤ_p) ⊆ p^{-L₀-M₀} ℤ_p`, so the bound
for `τ` gives `v_p(τ(P)) ≥ -6Λ - v_p(24)`. Each pole term `c_s (H_{d(s)}^{(5)} - X)` has
`v_p(c_s) ≥ -L₀ ≥ -Λ` and `v_p(H_{d(s)}^{(5)}) ≥ -5 ⌊log_p K⌋ ≥ -5Λ`, hence Gauss valuation at
least `-6Λ`. The ultrametric inequality for the Gauss valuation combines the terms.

## Main results

* `Zeta5Irr.le_vpG_tauX_factorial_sq_mul`: the bound
  `v_p^G(τ_X((K!)² A; R_K)) ≥ -6 ⌊log_p max(2K, d + 1)⌋ - v_p(24)`.

## Implementation notes

* `τ_X((K!)² A; R_K) ∈ ℚ[X]` is taken in `ℚ_p[X]` by mapping its coefficients along
  `ℚ → ℚ_p`, and `v_p^G` is `Zeta5Irr.vpG`, valued in `ℤ ∪ {∞}`.
* `⌊log_p n⌋` is `Nat.log p n` and `v_p(24)` is `padicValNat p 24`.
* The source assumes `K ≥ 2`; the argument does not use it, and the hypothesis is omitted.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

open Polynomial
open scoped Nat

namespace Zeta5Irr

variable {p : ℕ} [Fact p.Prime]

/-- A point of `R_K` has reflected index at most `K`. -/
theorem reflectIndex_le_of_mem_puncturedIcc {K : ℕ} {r : ℤ} (hr : r ∈ puncturedIcc K) :
    reflectIndex r ≤ K := by
  rcases le_or_gt 0 r with h0 | h0
  · have := reflectIndex_of_nonneg h0
    have := (mem_puncturedIcc.1 hr).2.2
    omega
  · have := reflectIndex_of_neg h0
    have := (mem_puncturedIcc.1 hr).2.1
    omega

/-- For `n ≤ K`, the Gauss valuation of `H_n^{(5)} - X` is at least `-5 ⌊log_p K⌋`. -/
theorem neg_five_mul_log_le_gaussAddVal_C_harmonicFive_sub_X {K n : ℕ} (hn : n ≤ K) :
    ((-5 * Nat.log p K : ℤ) : WithTop ℤ) ≤
      gaussAddVal Padic.addValuation (C (algebraMap ℚ ℚ_[p] (harmonicFive n)) - X) := by
  rw [le_gaussAddVal_iff]
  intro i
  rw [coeff_sub, coeff_C, coeff_X]
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [ite_true, show ¬ (1 = 0) from one_ne_zero, ite_false, sub_zero]
    rw [eq_ratCast]
    exact le_addValuation_harmonicFive hn
  · rcases eq_or_ne i 1 with rfl | h1
    · simp only [one_ne_zero, ite_false, ite_true, zero_sub, AddValuation.map_neg,
        AddValuation.map_one]
      rw [← WithTop.coe_zero, WithTop.coe_le_coe]
      omega
    · simp [hi, h1.symm]

/-- The polynomial term of `τ_X((K!)² A; R_K)` has `p`-adic valuation at least
`-6 ⌊log_p max(2K, d + 1)⌋ - v_p(24)`. -/
theorem le_vpG_C_tau_factorial_sq_mul_divByMonic {K d : ℕ} {A : ℚ[X]}
    (hA : ∀ m : ℤ, ∃ n : ℤ, A.eval (m : ℚ) = n) (hAd : A.natDegree ≤ d) :
    ((-6 * Nat.log p (max (2 * K) (d + 1)) - padicValNat p 24 : ℤ) : WithTop ℤ) ≤
      vpG (C (algebraMap ℚ ℚ_[p]
        (tau (C ((K ! : ℚ) ^ 2) * A /ₘ intPoleProduct (puncturedIcc K) ℚ)))) := by
  set Λ := Nat.log p (max (2 * K) (d + 1))
  set Q : ℚ[X] := C ((K ! : ℚ) ^ 2) * A with hQ
  set E := intPoleProduct (puncturedIcc K) ℚ
  have hL0 : Nat.log p (2 * K) ≤ Λ := Nat.log_mono_right (le_max_left _ _)
  have hLd : Nat.log p (d + 1) ≤ Λ := Nat.log_mono_right (le_max_right _ _)
  have hLm : Nat.log p (max 1 d) ≤ Λ := (Nat.log_mono_right (by omega)).trans hLd
  set f := algebraMap ℚ ℚ_[p]
  set A' := A.map f
  have hint : ∀ x : ℤ_[p], ‖A'.eval (x : ℚ_[p])‖ ≤ 1 := fun x ↦ by
    rw [eval_map_algebraMap]
    exact norm_aeval_padicInt_le_one hA x
  rw [vpG, gaussAddVal_C, eq_ratCast]
  have hPd : (Q /ₘ E).natDegree ≤ d := by
    rw [natDegree_divByMonic Q (monic_intPoleProduct _ ℚ)]
    exact (Nat.sub_le _ _).trans ((natDegree_C_mul_le _ _).trans hAd)
  have hdiv : C ((K ! : ℚ_[p]) ^ 2) * A' =
      (Q /ₘ E).map f * intPoleProduct (puncturedIcc K) ℚ_[p] + (Q %ₘ E).map f := by
    have h := congrArg (Polynomial.map f) (modByMonic_add_div Q E)
    rw [Polynomial.map_add, Polynomial.map_mul, map_intPoleProduct] at h
    have hQ' : C ((K ! : ℚ_[p]) ^ 2) * A' = Q.map f := by
      simp [hQ, A', f]
    rw [hQ', ← h]
    ring
  have hB : ((Q %ₘ E).map f).degree < ↑(2 * K) := by
    rw [degree_map]
    have := degree_modByMonic_lt Q (monic_intPoleProduct (puncturedIcc K) ℚ)
    rwa [degree_intPoleProduct, card_puncturedIcc] at this
  refine le_trans ?_ (le_addValuation_tau (β := Nat.log p (2 * K) +
    max (Nat.log p (2 * K) : ℤ) (Nat.log p (max 1 d))) hPd fun x ↦ ?_)
  · rw [WithTop.coe_le_coe]
    have : max (Nat.log p (2 * K) : ℤ) (Nat.log p (max 1 d)) ≤ Λ :=
      max_le (by exact_mod_cast hL0) (by exact_mod_cast hLm)
    push_cast
    omega
  · have := neg_log_sub_max_le_addValuation_eval (natDegree_map_le.trans hAd) hint hB hdiv x
    rw [eval_map_algebraMap] at this
    convert this using 2
    ring

/-- The pole term of `τ_X((K!)² A; R_K)` at `r ∈ R_K` has Gauss valuation at least
`-6 ⌊log_p(2K)⌋`. -/
theorem le_vpG_poleTerm_factorial_sq_mul {K : ℕ} {A : ℚ[X]}
    (hA : ∀ m : ℤ, ∃ n : ℤ, A.eval (m : ℚ) = n) {r : ℤ} (hr : r ∈ puncturedIcc K) :
    ((-6 * Nat.log p (2 * K) : ℤ) : WithTop ℤ) ≤
      vpG (C (algebraMap ℚ ℚ_[p] ((C ((K ! : ℚ) ^ 2) * A).eval (r : ℚ) /
          (derivative (intPoleProduct (puncturedIcc K) ℚ)).eval (r : ℚ))) *
        (C (algebraMap ℚ ℚ_[p] (harmonicFive (reflectIndex r))) - X)) := by
  set L := Nat.log p (2 * K)
  set f := algebraMap ℚ ℚ_[p]
  set A' := A.map f
  have hint : ∀ x : ℤ_[p], ‖A'.eval (x : ℚ_[p])‖ ≤ 1 := fun x ↦ by
    rw [eval_map_algebraMap]
    exact norm_aeval_padicInt_le_one hA x
  rw [vpG, gaussAddVal_C_mul]
  have hc : ((-L : ℤ) : WithTop ℤ) ≤ Padic.addValuation (f ((C ((K ! : ℚ) ^ 2) * A).eval (r : ℚ) /
      (derivative (intPoleProduct (puncturedIcc K) ℚ)).eval (r : ℚ))) := by
    have heq : f ((C ((K ! : ℚ) ^ 2) * A).eval (r : ℚ) /
        (derivative (intPoleProduct (puncturedIcc K) ℚ)).eval (r : ℚ)) =
        (K ! : ℚ_[p]) ^ 2 * A'.eval (r : ℚ_[p]) /
          (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p]) := by
      rw [map_div₀, ← map_intPoleProduct (f := f), derivative_map, eval_map, eval_map,
        ← Polynomial.eval₂_at_intCast, ← Polynomial.eval₂_at_intCast]
      simp [f, Polynomial.eval₂_at_intCast]
    rw [heq]
    set y := (K ! : ℚ_[p]) ^ 2 * A'.eval (r : ℚ_[p]) /
      (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p])
    rcases eq_or_ne y 0 with hy | hy
    · simp [hy]
    · rw [Padic.addValuation.apply hy, WithTop.coe_le_coe]
      have := neg_log_le_valuation_factorial_sq_mul_eval_div hint hr
      omega
  have hH := neg_five_mul_log_le_gaussAddVal_C_harmonicFive_sub_X (p := p)
    (reflectIndex_le_of_mem_puncturedIcc hr)
  have hLK : Nat.log p K ≤ L := Nat.log_mono_right (by omega)
  calc ((-6 * L : ℤ) : WithTop ℤ)
      ≤ ((-L + -5 * Nat.log p K : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.2 (by omega)
    _ = ((-L : ℤ) : WithTop ℤ) + ((-5 * Nat.log p K : ℤ) : WithTop ℤ) := WithTop.coe_add _ _
    _ ≤ _ := add_le_add hc hH

/-- **Small primes.** Let `A ∈ ℚ[x]` take integer values at the integers and have degree at
most `d`. Then `v_p^G(τ_X((K!)² A; R_K)) ≥ -6 ⌊log_p max(2K, d + 1)⌋ - v_p(24)`. -/
@[zeta5irr "lem_small_prime"]
theorem le_vpG_tauX_factorial_sq_mul {K d : ℕ} {A : ℚ[X]}
    (hA : ∀ m : ℤ, ∃ n : ℤ, A.eval (m : ℚ) = n) (hAd : A.natDegree ≤ d) :
    ((-6 * Nat.log p (max (2 * K) (d + 1)) - padicValNat p 24 : ℤ) : WithTop ℤ) ≤
      vpG ((tauX (puncturedIcc K) (C ((K ! : ℚ) ^ 2) * A)).map (algebraMap ℚ ℚ_[p])) := by
  have hL0 : Nat.log p (2 * K) ≤ Nat.log p (max (2 * K) (d + 1)) :=
    Nat.log_mono_right (le_max_left _ _)
  have hv24 : (0 : ℤ) ≤ padicValNat p 24 := by positivity
  simp only [tauX, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X]
  refine le_trans (le_min (le_vpG_C_tau_factorial_sq_mul_divByMonic hA hAd) ?_)
    (min_le_vpG_add _ _)
  refine (Finset.le_inf fun r hr ↦ ?_).trans (finset_inf_le_gaussAddVal_sum _ _ _)
  exact (WithTop.coe_le_coe.2 (by omega)).trans (le_vpG_poleTerm_factorial_sq_mul hA hr)

end Zeta5Irr
