/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.QRK
public import Zeta5Irr.LocalFunctional.SmallRootcount
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The local functional at a small prime, away from `R_K`

Let `p` be a prime, `K ∈ ℕ`, `L₀ = ⌊log_p(2K)⌋`, `A ∈ ℚ_p[x]`, and let `x ∈ ℤ_p` satisfy
`A(x) ∈ ℤ_p` and `v_p(x - s) ≤ L₀` for every `s ∈ R_K = {s ∈ ℤ : -K ≤ s ≤ K, s ≠ 0}`. Then
`E_{R_K}(x) = ∏_{s ∈ R_K} (x - s)` is nonzero and
`v_p((K!)² A(x) / E_{R_K}(x)) ≥ -2 L₀`.

Since every `v_p(x - s)` is at most `L₀`, counting `s` once for each `1 ≤ i ≤ v_p(x - s)` gives
`v_p(E_{R_K}(x)) = ∑_{i=1}^{L₀} #{s ∈ R_K : v_p(x - s) ≥ i} ≤ ∑_{i=1}^{L₀} (⌊2K/p^i⌋ + 1)`,
while Legendre's formula gives `2 v_p(K!) = ∑_{i=1}^{L₀} 2⌊K/p^i⌋` and
`⌊2K/p^i⌋ ≤ 2⌊K/p^i⌋ + 1`.

## Main results

* `Zeta5Irr.eval_intPoleProduct_puncturedIcc_ne_zero`: `E_{R_K}(x) ≠ 0`.
* `Zeta5Irr.valuation_eval_intPoleProduct_puncturedIcc_le`:
  `v_p(E_{R_K}(x)) ≤ ∑_{i=1}^{L₀} (⌊2K/p^i⌋ + 1)`.
* `Zeta5Irr.neg_two_log_le_valuation_factorial_sq_mul_eval_div`:
  `v_p((K!)² A(x) / E_{R_K}(x)) ≥ -2 L₀`.

## Implementation notes

* The hypothesis `v_p(x - s) ≤ L₀` (with `v_p(0) = ∞`) is stated as
  `¬ p^{L₀+1} ∣ x - s` in `ℤ_p`, as in `Zeta5Irr.card_filter_puncturedIcc_pow_dvd_sub_le`.
* The valuation is `Padic.valuation : ℚ_[p] → ℤ`, which is `0` at `0`; when `A(x) = 0` the
  bound holds since `-2 L₀ ≤ 0`.
* The source assumes `A(ℤ_p) ⊆ ℤ_p`; only `A(x) ∈ ℤ_p`, i.e. `‖A(x)‖ ≤ 1`, is used. The
  hypothesis `K ≥ 1` is not needed. `⌊log_p(2K)⌋` is `Nat.log p (2 * K)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset Nat

/-- The valuation on `ℤ_p` of a finite product of nonzero elements is the sum of their
valuations. -/
theorem padicInt_valuation_prod {p : ℕ} [Fact p.Prime] {ι : Type*} {S : Finset ι}
    {f : ι → ℤ_[p]} (hf : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i).valuation = ∑ i ∈ S, (f i).valuation := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [prod_insert ha, sum_insert ha, PadicInt.valuation_mul (hf a (mem_insert_self _ _))
      (prod_ne_zero_iff.2 fun i hi ↦ hf i (mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (mem_insert_of_mem hi)]

/-- For `z ≠ 0` in `ℤ_p`, `p^n ∣ z` if and only if `n ≤ v_p(z)`. -/
theorem padicInt_pow_dvd_iff_le_valuation {p : ℕ} [Fact p.Prime] {z : ℤ_[p]} (hz : z ≠ 0)
    (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ z ↔ n ≤ z.valuation := by
  rw [← PadicInt.mem_span_pow_iff_le_valuation z hz, Ideal.mem_span_singleton]

open scoped Classical in
/-- If `z ≠ 0` in `ℤ_p` has `v_p(z) ≤ L`, that is `p^{L+1} ∤ z`, then
`v_p(z) = #{i : 1 ≤ i ≤ L, p^i ∣ z}`. -/
theorem padicInt_valuation_eq_card_filter_pow_dvd {p : ℕ} [Fact p.Prime] {z : ℤ_[p]}
    (hz : z ≠ 0) {L : ℕ} (hL : ¬ (p : ℤ_[p]) ^ (L + 1) ∣ z) :
    z.valuation = #{i ∈ Ico 1 (L + 1) | (p : ℤ_[p]) ^ i ∣ z} := by
  rw [padicInt_pow_dvd_iff_le_valuation hz, not_le] at hL
  have : {i ∈ Ico 1 (L + 1) | (p : ℤ_[p]) ^ i ∣ z} = Ico 1 (z.valuation + 1) := by
    ext i
    simp only [mem_filter, mem_Ico, padicInt_pow_dvd_iff_le_valuation hz]
    omega
  rw [this, Nat.card_Ico]
  omega

/-- If `v_p(x - s) ≤ ⌊log_p(2K)⌋` for every `s ∈ R_K`, then `x ≠ s` for every `s ∈ R_K`. -/
theorem sub_intCast_ne_zero_of_not_pow_dvd {p : ℕ} [Fact p.Prime] {K : ℕ} {x : ℤ_[p]}
    (hx : ∀ s ∈ puncturedIcc K, ¬ (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - s)
    {s : ℤ} (hs : s ∈ puncturedIcc K) : x - s ≠ 0 := by
  intro h
  exact hx s hs (h ▸ dvd_zero _)

/-- **Small primes, points outside `R_K`: non-vanishing.** If `x ∈ ℤ_p` satisfies
`v_p(x - s) ≤ ⌊log_p(2K)⌋` for every `s ∈ R_K`, then `E_{R_K}(x) ≠ 0`. -/
@[zeta5irr "lem_small_outside"]
theorem eval_intPoleProduct_puncturedIcc_ne_zero {p : ℕ} [Fact p.Prime] {K : ℕ} {x : ℤ_[p]}
    (hx : ∀ s ∈ puncturedIcc K, ¬ (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - s) :
    (intPoleProduct (puncturedIcc K) ℚ_[p]).eval (x : ℚ_[p]) ≠ 0 := by
  rw [eval_intPoleProduct, prod_ne_zero_iff]
  intro s hs
  have := sub_intCast_ne_zero_of_not_pow_dvd hx hs
  rw [← PadicInt.coe_intCast, ← PadicInt.coe_sub]
  exact PadicInt.coe_ne_zero.2 this

/-- If `x ∈ ℤ_p` satisfies `v_p(x - s) ≤ L₀ = ⌊log_p(2K)⌋` for every `s ∈ R_K`, then
`v_p(E_{R_K}(x)) ≤ ∑_{i=1}^{L₀} (⌊2K/p^i⌋ + 1)`. -/
theorem valuation_eval_intPoleProduct_puncturedIcc_le {p : ℕ} [Fact p.Prime] {K : ℕ}
    {x : ℤ_[p]}
    (hx : ∀ s ∈ puncturedIcc K, ¬ (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - s) :
    ((intPoleProduct (puncturedIcc K) ℚ_[p]).eval (x : ℚ_[p])).valuation ≤
      ∑ i ∈ Ico 1 (Nat.log p (2 * K) + 1), (2 * K / p ^ i + 1 : ℕ) := by
  classical
  have hE : (intPoleProduct (puncturedIcc K) ℚ_[p]).eval (x : ℚ_[p]) =
      ((∏ s ∈ puncturedIcc K, (x - (s : ℤ_[p])) : ℤ_[p]) : ℚ_[p]) := by
    rw [eval_intPoleProduct,
      show ((∏ s ∈ puncturedIcc K, (x - (s : ℤ_[p])) : ℤ_[p]) : ℚ_[p]) =
        PadicInt.Coe.ringHom (∏ s ∈ puncturedIcc K, (x - (s : ℤ_[p]))) from rfl, map_prod]
    simp only [map_sub, map_intCast]
    rfl
  rw [hE, PadicInt.valuation_coe, padicInt_valuation_prod fun s hs ↦
    sub_intCast_ne_zero_of_not_pow_dvd hx hs]
  norm_cast
  calc ∑ s ∈ puncturedIcc K, (x - (s : ℤ_[p])).valuation
      = ∑ s ∈ puncturedIcc K, #{i ∈ Ico 1 (Nat.log p (2 * K) + 1) |
          (p : ℤ_[p]) ^ i ∣ x - (s : ℤ_[p])} :=
        sum_congr rfl fun s hs ↦
          padicInt_valuation_eq_card_filter_pow_dvd (sub_intCast_ne_zero_of_not_pow_dvd hx hs)
            (hx s hs)
    _ = ∑ i ∈ Ico 1 (Nat.log p (2 * K) + 1),
          #{s ∈ puncturedIcc K | (p : ℤ_[p]) ^ i ∣ x - ((s : ℤ) : ℤ_[p])} := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ _ := sum_le_sum fun i _ ↦ card_filter_puncturedIcc_pow_dvd_sub_le p K i x

/-- **Small primes, points outside `R_K`: the valuation bound.** Let `p` be a prime,
`A ∈ ℚ_p[x]`, and `x ∈ ℤ_p` with `A(x) ∈ ℤ_p` and `v_p(x - s) ≤ ⌊log_p(2K)⌋` for every
`s ∈ R_K`. Then `v_p((K!)² A(x) / E_{R_K}(x)) ≥ -2⌊log_p(2K)⌋`. -/
@[zeta5irr "lem_small_outside"]
theorem neg_two_log_le_valuation_factorial_sq_mul_eval_div {p : ℕ} [Fact p.Prime] {K : ℕ}
    {A : ℚ_[p][X]} {x : ℤ_[p]} (hA : ‖A.eval (x : ℚ_[p])‖ ≤ 1)
    (hx : ∀ s ∈ puncturedIcc K, ¬ (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - s) :
    -(2 * Nat.log p (2 * K) : ℤ) ≤ Padic.valuation ((K ! : ℚ_[p]) ^ 2 * A.eval (x : ℚ_[p]) /
      (intPoleProduct (puncturedIcc K) ℚ_[p]).eval (x : ℚ_[p])) := by
  have hE0 := eval_intPoleProduct_puncturedIcc_ne_zero hx
  have hvE := valuation_eval_intPoleProduct_puncturedIcc_le hx
  set y := A.eval (x : ℚ_[p])
  by_cases hy : y = 0
  · simp [hy]
  have hy1 : 0 ≤ y.valuation := by
    rw [← Padic.norm_le_one_iff_val_nonneg]
    exact hA
  have hLeg : padicValNat p K ! = ∑ i ∈ Ico 1 (Nat.log p (2 * K) + 1), K / p ^ i :=
    padicValNat_factorial (Nat.lt_succ_of_le (Nat.log_mono_right (by omega)))
  have hsum : ∑ i ∈ Ico 1 (Nat.log p (2 * K) + 1), (2 * K / p ^ i + 1 : ℕ) ≤
      2 * padicValNat p K ! + 2 * Nat.log p (2 * K) := by
    rw [hLeg, mul_sum]
    calc ∑ i ∈ Ico 1 (Nat.log p (2 * K) + 1), (2 * K / p ^ i + 1 : ℕ)
        ≤ ∑ i ∈ Ico 1 (Nat.log p (2 * K) + 1), (2 * (K / p ^ i) + 2) := by
          refine sum_le_sum fun i _ ↦ ?_
          have hn : 0 < p ^ i := pow_pos (Fact.out : p.Prime).pos i
          have h1 := Nat.lt_mul_div_succ K hn
          have h2 : 2 * K / p ^ i < 2 * (K / p ^ i) + 2 :=
            (Nat.div_lt_iff_lt_mul hn).2 (by nlinarith)
          omega
      _ = _ := by simp [sum_add_distrib, Nat.card_Ico, mul_comm]
  rw [div_eq_mul_inv, Padic.valuation_mul (by simp [hy, factorial_ne_zero]) (inv_ne_zero hE0),
    Padic.valuation_mul (by simp [factorial_ne_zero]) hy, Padic.valuation_inv, ← Nat.cast_pow,
    Padic.valuation_natCast, Nat.pow_two, padicValNat.mul (by positivity) (by positivity)]
  have : ((intPoleProduct (puncturedIcc K) ℚ_[p]).eval (x : ℚ_[p])).valuation ≤
      2 * padicValNat p K ! + 2 * Nat.log p (2 * K) :=
    hvE.trans (by exact_mod_cast hsum)
  rw [Nat.cast_add]
  omega

end Zeta5Irr
