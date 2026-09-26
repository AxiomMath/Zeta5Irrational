/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.QRK
public import Zeta5Irr.LocalFunctional.DerivProdEval
public import Zeta5Irr.LocalFunctional.FloorAddSub
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The valuation of a residue at a small prime

Let `p` be a prime, `K ≥ 1`, `A ∈ ℚ_p[x]` with `A(ℤ_p) ⊆ ℤ_p`, and `r ∈ R_K`, where
`R_K = {s ∈ ℤ : -K ≤ s ≤ K, s ≠ 0}`. Then
`v_p((K!)² A(r) / E_{R_K}'(r)) ≥ -⌊log_p(2K)⌋`.

The derivative of `E_{R_K} = ∏_{s ∈ R_K} (x - s)` at the root `r` is
`∏_{s ∈ R_K \ {r}} (r - s)`, and multiplying by the missing factor `r - 0 = r` gives
`r E_{R_K}'(r) = (-1)^{K-r} (K+r)! (K-r)!`. Hence
`v_p(E_{R_K}'(r)) ≤ v_p((K+r)!) + v_p((K-r)!)`, and by Legendre's formula with
`L₀ = ⌊log_p(2K)⌋`,
`v_p((K+r)!) + v_p((K-r)!) - 2 v_p(K!) = ∑_{i=1}^{L₀} (⌊(K+r)/p^i⌋ + ⌊(K-r)/p^i⌋ - 2⌊K/p^i⌋)`,
each summand being at most `1`.

## Main results

* `Zeta5Irr.prod_erase_range_natCast_sub`:
  `∏_{i ∈ {0,…,N} \ {a}} (a - i) = (-1)^{N-a} a! (N-a)!` for `a ≤ N`.
* `Zeta5Irr.mul_prod_erase_puncturedIcc_sub`:
  `r ∏_{s ∈ R_K \ {r}} (r - s) = (-1)^{K-r} (K+r)! (K-r)!` for `r ∈ R_K`.
* `Zeta5Irr.padicValNat_factorial_add_le`:
  `v_p((K+r)!) + v_p((K-r)!) ≤ 2 v_p(K!) + ⌊log_p(2K)⌋`.
* `Zeta5Irr.neg_log_le_valuation_factorial_sq_mul_eval_div`: the main bound.

## Implementation notes

* The valuation is `Padic.valuation : ℚ_[p] → ℤ`, which takes the value `0` at `0` instead of
  `∞`. When `A(r) = 0` the source's statement is trivially true, and so is this one, since
  `-⌊log_p(2K)⌋ ≤ 0`.
* `⌊log_p(2K)⌋` is `Nat.log p (2 * K)`. The hypothesis `K ≥ 1` of the source is implied by
  `r ∈ R_K` and is omitted.
* The natural numbers `K + r` and `K - r` are written `(K + r).toNat` and `(K - r).toNat`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset Nat

/-- For `a ≤ N`, `∏_{i ∈ {0,…,N} \ {a}} (a - i) = (-1)^{N-a} a! (N-a)!`. -/
theorem prod_erase_range_natCast_sub {R : Type*} [CommRing R] {a N : ℕ} (h : a ≤ N) :
    ∏ i ∈ (range (N + 1)).erase a, ((a : R) - i) = (-1) ^ (N - a) * a ! * (N - a)! := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [range_add_one, erase_insert notMem_range_self, Nat.sub_self, pow_zero, one_mul,
      factorial_zero, Nat.cast_one, mul_one, ← Nat.descFactorial_self,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine prod_congr rfl fun i hi ↦ ?_
    rw [Nat.cast_sub (mem_range.1 hi).le]
  | succ N hN ih =>
    rw [range_add_one (n := N + 1), erase_insert_of_ne (by omega), prod_insert (by simp), ih,
      Nat.sub_add_comm hN, pow_succ, factorial_succ]
    push_cast [Nat.cast_sub hN]
    ring

/-- For `r ∈ R_K`, the product `∏_{s ∈ R_K \ {r}} (r - s)` times the missing factor `r - 0` is
`r ∏_{s ∈ R_K \ {r}} (r - s) = (-1)^{K-r} (K+r)! (K-r)!`. -/
theorem mul_prod_erase_puncturedIcc_sub {R : Type*} [CommRing R] {K : ℕ} {r : ℤ}
    (hr : r ∈ puncturedIcc K) :
    (r : R) * ∏ s ∈ (puncturedIcc K).erase r, ((r : R) - s) =
      (-1) ^ (K - r).toNat * (K + r).toNat ! * (K - r).toNat ! := by
  rw [mem_puncturedIcc] at hr
  have h0 : (0 : ℤ) ∈ (Icc (-(K : ℤ)) K).erase r := by simp; omega
  have key : (r : R) * ∏ s ∈ (puncturedIcc K).erase r, ((r : R) - s) =
      ∏ s ∈ (Icc (-(K : ℤ)) K).erase r, ((r : R) - s) := by
    rw [← mul_prod_erase _ _ h0, puncturedIcc, erase_right_comm]
    simp
  rw [key]
  have ha : (K + r).toNat ≤ 2 * K := by omega
  have hb : 2 * K - (K + r).toNat = (K - r).toNat := by omega
  rw [← hb, ← prod_erase_range_natCast_sub ha]
  refine prod_nbij' (fun s ↦ (s + K).toNat) (fun i ↦ (i : ℤ) - K) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_erase, mem_Icc, mem_range] at hs ⊢
    omega
  · intro i hi
    simp only [mem_erase, mem_Icc, mem_range] at hi ⊢
    omega
  · intro s hs
    simp only [mem_erase, mem_Icc] at hs
    omega
  · intro i hi
    omega
  · intro s hs
    simp only [mem_erase, mem_Icc] at hs
    have e1 : (((K + r).toNat : ℕ) : ℤ) = K + r := by omega
    have e2 : (((s + K).toNat : ℕ) : ℤ) = s + K := by omega
    rw [← Int.cast_natCast (R := R), ← Int.cast_natCast (R := R) (s + K).toNat, e1, e2]
    push_cast
    ring

/-- Legendre's formula and the floor inequality `⌊(K+r)/n⌋ + ⌊(K-r)/n⌋ ≤ 2⌊K/n⌋ + 1` give
`v_p((K+r)!) + v_p((K-r)!) ≤ 2 v_p(K!) + ⌊log_p(2K)⌋` for `|r| ≤ K`. -/
theorem padicValNat_factorial_add_le {p : ℕ} [Fact p.Prime] {K : ℕ} {r : ℤ}
    (hr : |r| ≤ K) :
    padicValNat p (K + r).toNat ! + padicValNat p (K - r).toNat ! ≤
      2 * padicValNat p K ! + Nat.log p (2 * K) := by
  rw [abs_le] at hr
  have hlog {n : ℕ} (hn : n ≤ 2 * K) : Nat.log p n < Nat.log p (2 * K) + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right hn)
  rw [padicValNat_factorial (hlog (n := (K + r).toNat) (by omega)),
    padicValNat_factorial (hlog (n := (K - r).toNat) (by omega)),
    padicValNat_factorial (hlog (n := K) (by omega)), ← sum_add_distrib, mul_sum]
  refine (sum_le_sum (g := fun i ↦ 2 * (K / p ^ i) + 1) fun i _ ↦ ?_).trans ?_
  swap
  · rw [sum_add_distrib]
    simp
  have h := add_ediv_add_sub_ediv_le ((p ^ i : ℕ) : ℤ) K r
  have e1 : (((K + r).toNat / p ^ i : ℕ) : ℤ) = (K + r) / ((p ^ i : ℕ) : ℤ) := by
    rw [Int.natCast_div]; congr 1; omega
  have e2 : (((K - r).toNat / p ^ i : ℕ) : ℤ) = (K - r) / ((p ^ i : ℕ) : ℤ) := by
    rw [Int.natCast_div]; congr 1; omega
  have e3 : ((K / p ^ i : ℕ) : ℤ) = (K : ℤ) / ((p ^ i : ℕ) : ℤ) := Int.natCast_div _ _
  omega

/-- **Valuation of a residue at a small prime.** Let `p` be a prime, `A ∈ ℚ_p[x]` with
`A(ℤ_p) ⊆ ℤ_p`, and `r ∈ R_K`. Then
`v_p((K!)² A(r) / E_{R_K}'(r)) ≥ -⌊log_p(2K)⌋`. -/
@[zeta5irr "lem_small_res_val"]
theorem neg_log_le_valuation_factorial_sq_mul_eval_div {p : ℕ} [Fact p.Prime] {K : ℕ}
    {A : ℚ_[p][X]} (hA : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) {r : ℤ}
    (hr : r ∈ puncturedIcc K) :
    -(Nat.log p (2 * K) : ℤ) ≤ Padic.valuation ((K ! : ℚ_[p]) ^ 2 * A.eval (r : ℚ_[p]) /
      (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p])) := by
  set D : ℤ := ∏ s ∈ (puncturedIcc K).erase r, (r - s) with hD
  have hE : (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p]) =
      (D : ℚ_[p]) := by
    rw [intPoleProduct, eval_derivative_prod_X_sub_C _ (fun s : ℤ ↦ (s : ℚ_[p])) hr, hD]
    push_cast
    rfl
  have hr0 : r ≠ 0 := ne_zero_of_mem_puncturedIcc hr
  have hmul := mul_prod_erase_puncturedIcc_sub (R := ℤ) hr
  simp only [Int.cast_id] at hmul
  rw [← hD] at hmul
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
      (by positivity)) hmul.symm
  -- `v_p(D) ≤ v_p((K+r)!) + v_p((K-r)!)`
  have hvD : (padicValInt p D : ℤ) ≤
      padicValNat p (K + r).toNat ! + padicValNat p (K - r).toNat ! := by
    have h1 := congrArg (padicValInt p) hmul
    rw [padicValInt.mul hr0 hD0, padicValInt.mul (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by positivity)) (by positivity), padicValInt.mul (pow_ne_zero _ (by norm_num))
      (by positivity)] at h1
    simp only [padicValInt.of_nat] at h1
    have : padicValInt p ((-1) ^ (K - r).toNat) = 0 := by
      simp [padicValInt, Int.natAbs_pow]
    omega
  have hLeg := padicValNat_factorial_add_le (p := p) (abs_le_of_mem_puncturedIcc hr)
  set y := A.eval (r : ℚ_[p])
  by_cases hy : y = 0
  · simp [hy]
  have hy1 : 0 ≤ y.valuation := by
    rw [← Padic.norm_le_one_iff_val_nonneg]
    simpa using hA (r : ℤ_[p])
  rw [hE, div_eq_mul_inv, Padic.valuation_mul (by simp [hy, factorial_ne_zero]) (by simp [hD0]),
    Padic.valuation_mul (by simp [factorial_ne_zero]) hy, Padic.valuation_inv, ← Nat.cast_pow,
    Padic.valuation_natCast, Padic.valuation_intCast, Nat.pow_two,
    padicValNat.mul (by positivity) (by positivity)]
  rw [Nat.cast_add]
  omega

end Zeta5Irr
