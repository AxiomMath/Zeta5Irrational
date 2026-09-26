/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Fr
public import Zeta5Irr.LocalFunctional.SmallResVal

/-!
# The valuation of `F_{K,r}` near its deleted pole at a small prime

Let `p` be a prime, `K ≥ 1`, `r ∈ R_K` and `L₀ = ⌊log_p(2K)⌋`, and let `x ∈ ℤ_p` satisfy
`v_p(x - r) ≥ L₀ + 1`. Then the denominator `∏_{s ∈ R_K \ {r}} (x - s)` of the pole-deleted
product `F_{K,r}` does not vanish at `x`, and `v_p(F_{K,r}(x)) ≥ -L₀`.

For `s ∈ R_K \ {r}` we have `0 < |r - s| ≤ 2K < p^{L₀+1}`, so `v_p(r - s) ≤ L₀ < v_p(x - r)`,
and the ultrametric equality gives `‖x - s‖ = ‖r - s‖`. Hence
`‖F_{K,r}(x)‖ = ‖(K!)² / ∏_{s ≠ r} (r - s)‖ = ‖(K!)² / E_{R_K}'(r)‖`, and the bound is the
case `A = 1` of the valuation bound for residues at small primes.

## Main results

* `Zeta5Irr.zpow_lt_norm_intCast_sub`: distinct `r, s ∈ R_K` satisfy
  `p^{-(⌊log_p(2K)⌋ + 1)} < ‖r - s‖`.
* `Zeta5Irr.norm_sub_intCast_le_of_pow_dvd`: `p ^ m ∣ x - r` gives `‖x - r‖ ≤ p^{-m}`.
* `Zeta5Irr.norm_sub_intCast_eq_of_mem_erase_puncturedIcc`: `‖x - s‖ = ‖r - s‖` for
  `s ∈ R_K \ {r}`.
* `Zeta5Irr.eval_poleDeletedDen_ne_zero_of_dvd`: the denominator of `F_{K,r}` does not vanish
  at `x`.
* `Zeta5Irr.neg_log_le_valuation_poleDeletedProductAt`: `v_p(F_{K,r}(x)) ≥ -⌊log_p(2K)⌋`.
* `Zeta5Irr.neg_log_le_valuation_eval_poleDeletedProduct`: the same bound for the value at `x`
  of the rational function `F_{K,r} ∈ ℚ(x)`.

## Implementation notes

* The hypothesis `v_p(x - r) ≥ L₀ + 1` is written `p ^ (L₀ + 1) ∣ x - r` in `ℤ_[p]`, which
  also covers `x = r`.
* `⌊log_p(2K)⌋` is `Nat.log p (2 * K)`, and the valuation is `Padic.valuation`. The hypothesis
  `K ≥ 1` of the source is implied by `r ∈ R_K` and is omitted.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset Nat

variable {p : ℕ} [Fact p.Prime] {K : ℕ} {r : ℤ} {x : ℤ_[p]}

/-- For distinct `r, s ∈ R_K`, `v_p(r - s) ≤ ⌊log_p(2K)⌋`, in the form
`p^{-(⌊log_p(2K)⌋ + 1)} < ‖r - s‖`, since `0 < |r - s| ≤ 2K < p^{⌊log_p(2K)⌋ + 1}`. -/
theorem zpow_lt_norm_intCast_sub {r s : ℤ} (hr : r ∈ puncturedIcc K)
    (hs : s ∈ (puncturedIcc K).erase r) :
    (p : ℝ) ^ (-((Nat.log p (2 * K) : ℤ) + 1)) < ‖((r - s : ℤ) : ℚ_[p])‖ := by
  set L := Nat.log p (2 * K)
  obtain ⟨hsr, hsK⟩ := mem_erase.1 hs
  have hsK' := mem_puncturedIcc.1 hsK
  have hr' := mem_puncturedIcc.1 hr
  have hlt : 2 * K < p ^ (L + 1) := Nat.lt_pow_succ_log_self (Fact.out : p.Prime).one_lt _
  by_contra h
  rw [not_lt, show -((L : ℤ) + 1) = -((L + 1 : ℕ) : ℤ) by push_cast; ring,
    Padic.norm_int_le_pow_iff_dvd] at h
  have hc : ((p ^ (L + 1) : ℕ) : ℤ) = (p : ℤ) ^ (L + 1) := by push_cast; rfl
  have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; omega)
  omega

/-- If `p ^ m ∣ x - r` in `ℤ_p`, then `‖x - r‖ ≤ p^{-m}`. -/
theorem norm_sub_intCast_le_of_pow_dvd {r : ℤ} {m : ℕ} (h : (p : ℤ_[p]) ^ m ∣ x - r) :
    ‖(x : ℚ_[p]) - r‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow (x - (r : ℤ_[p])) m).2
    (Ideal.mem_span_singleton.2 h)
  simpa [PadicInt.norm_def] using h

/-- If `r ∈ R_K` and `v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1`, then `‖x - s‖ = ‖r - s‖` for every
`s ∈ R_K \ {r}`. -/
theorem norm_sub_intCast_eq_of_mem_erase_puncturedIcc (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) {s : ℤ}
    (hs : s ∈ (puncturedIcc K).erase r) :
    ‖(x : ℚ_[p]) - s‖ = ‖((r - s : ℤ) : ℚ_[p])‖ := by
  have hrs := zpow_lt_norm_intCast_sub (p := p) hr hs
  have hxr : ‖((x : ℚ_[p]) - r)‖ ≤ (p : ℝ) ^ (-((Nat.log p (2 * K) : ℤ) + 1)) := by
    simpa using norm_sub_intCast_le_of_pow_dvd hx
  have e : (x : ℚ_[p]) - s = ((x : ℚ_[p]) - r) + ((r - s : ℤ) : ℚ_[p]) := by push_cast; ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hxr.trans_lt hrs).ne,
    max_eq_right (hxr.trans hrs.le)]

/-- If `r ∈ R_K` and `v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1`, then
`‖∏_{s ∈ R_K \ {r}} (x - s)‖ = ‖∏_{s ∈ R_K \ {r}} (r - s)‖`. -/
theorem norm_prod_sub_eq_of_dvd (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) :
    ‖∏ s ∈ (puncturedIcc K).erase r, ((x : ℚ_[p]) - s)‖ =
      ‖((∏ s ∈ (puncturedIcc K).erase r, (r - s) : ℤ) : ℚ_[p])‖ := by
  rw [Int.cast_prod, norm_prod, norm_prod]
  exact prod_congr rfl fun s hs ↦ norm_sub_intCast_eq_of_mem_erase_puncturedIcc hr hx hs

/-- **The denominator of `F_{K,r}` does not vanish near `r`.** If `r ∈ R_K` and
`v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1`, then `∏_{s ∈ R_K \ {r}} (x - s) ≠ 0`. -/
@[zeta5irr "lem_small_Fr_val"]
theorem eval_poleDeletedDen_ne_zero_of_dvd (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) :
    (poleDeletedDen ℚ_[p] K r).eval (x : ℚ_[p]) ≠ 0 := by
  rw [eval_intPoleProduct, ← norm_ne_zero_iff, norm_prod_sub_eq_of_dvd hr hx, norm_ne_zero_iff,
    Int.cast_ne_zero, prod_ne_zero_iff]
  intro s hs
  exact sub_ne_zero.2 (ne_of_mem_erase hs).symm

/-- **Valuation of `F_{K,r}` near its deleted pole at a small prime.** If `r ∈ R_K` and
`v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1`, then `v_p(F_{K,r}(x)) ≥ -⌊log_p(2K)⌋`. -/
@[zeta5irr "lem_small_Fr_val"]
theorem neg_log_le_valuation_poleDeletedProductAt (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) :
    -(Nat.log p (2 * K) : ℤ) ≤ Padic.valuation (poleDeletedProductAt K r (x : ℚ_[p])) := by
  have hP := eval_poleDeletedDen_ne_zero_of_dvd hr hx
  rw [eval_intPoleProduct] at hP
  set D : ℤ := ∏ s ∈ (puncturedIcc K).erase r, (r - s) with hD
  have hE : (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p]) =
      (D : ℚ_[p]) := by
    rw [intPoleProduct, eval_derivative_prod_X_sub_C _ (fun s : ℤ ↦ (s : ℚ_[p])) hr, hD]
    push_cast
    rfl
  have h := neg_log_le_valuation_factorial_sq_mul_eval_div (p := p) (A := 1)
    (fun _ ↦ by simp) hr
  rw [eval_one, mul_one, hE] at h
  have hK : (K ! : ℚ_[p]) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 K.factorial_ne_zero)
  have hD0 : (D : ℚ_[p]) ≠ 0 := by
    rw [← norm_ne_zero_iff, hD, ← norm_prod_sub_eq_of_dvd hr hx, norm_ne_zero_iff]
    exact hP
  have hn : ‖poleDeletedProductAt K r (x : ℚ_[p])‖ = ‖(K ! : ℚ_[p]) ^ 2 / D‖ := by
    rw [poleDeletedProductAt, norm_div, norm_div, norm_prod_sub_eq_of_dvd hr hx]
  have h1 : poleDeletedProductAt K r (x : ℚ_[p]) ≠ 0 := div_ne_zero hK hP
  have h2 : (K ! : ℚ_[p]) ^ 2 / D ≠ 0 := div_ne_zero hK hD0
  rw [Padic.norm_eq_zpow_neg_valuation h1, Padic.norm_eq_zpow_neg_valuation h2] at hn
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp.ne' hn
  omega

/-- The bound `v_p(F_{K,r}(x)) ≥ -⌊log_p(2K)⌋` for the value at `x` of the rational function
`F_{K,r} ∈ ℚ(x)`, evaluated along the embedding `ℚ → ℚ_p`. -/
theorem neg_log_le_valuation_eval_poleDeletedProduct (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) :
    -(Nat.log p (2 * K) : ℤ) ≤
      Padic.valuation ((poleDeletedProduct K r).eval (algebraMap ℚ ℚ_[p]) (x : ℚ_[p])) := by
  rw [eval_poleDeletedProduct _ ((eval_intPoleProduct_ne_zero_iff _ _).1
    (eval_poleDeletedDen_ne_zero_of_dvd hr hx))]
  exact neg_log_le_valuation_poleDeletedProductAt hr hx

end Zeta5Irr
