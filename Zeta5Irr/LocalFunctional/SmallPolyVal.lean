/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.QRK
public import Zeta5Irr.LocalFunctional.TauPf
public import Zeta5Irr.LocalFunctional.SmallDiff
public import Zeta5Irr.LocalFunctional.SmallOutside
public import Zeta5Irr.LocalFunctional.SmallFrDiff

/-!
# The valuation of the quotient polynomial at a small prime

Let `p` be a prime, `K ∈ ℕ`, `d ∈ ℕ`, and let `A ∈ ℚ_p[x]` have degree at most `d` and satisfy
`A(ℤ_p) ⊆ ℤ_p`. Suppose `(K!)² A = P E_{R_K} + B` with `P, B ∈ ℚ_p[x]` and `deg B < 2K`, where
`R_K = {s ∈ ℤ : -K ≤ s ≤ K, s ≠ 0}` and `E_{R_K} = ∏_{s ∈ R_K} (x - s)`. Write
`L₀ = ⌊log_p(2K)⌋` and `M₀ = max(L₀, ⌊log_p max(1, d)⌋)`. Then `v_p(P(x)) ≥ -L₀ - M₀` for every
`x ∈ ℤ_p`.

With `c_s = (K!)² A(s) / E_{R_K}'(s)`, the partial fraction decomposition gives
`P(x) = (K!)² A(x) / E_{R_K}(x) - ∑_{s ∈ R_K} c_s / (x - s)` away from `R_K`. If
`v_p(x - s) ≤ L₀` for all `s`, every term has valuation at least `-2 L₀`. If
`v_p(x - r) ≥ L₀ + 1` for some `r ∈ R_K` with `x ≠ r`, the two terms carrying the pole at `r`
combine into `((A(x) - A(r)) F_{K,r}(x) + A(r) (F_{K,r}(x) - F_{K,r}(r))) / (x - r)`, which is
bounded using the difference bounds for `A` and for `F_{K,r}`. The remaining case `x = r` follows
by continuity of `P`.

## Main results

* `Zeta5Irr.eval_eq_div_sub_sum_of_eq_mul_add`: the partial fraction formula for `P(x)`.
* `Zeta5Irr.norm_eval_le_of_forall_not_pow_dvd`: `‖P(x)‖ ≤ p^{2 L₀}` when `v_p(x - s) ≤ L₀` for
  all `s ∈ R_K`.
* `Zeta5Irr.norm_eval_le_of_pow_dvd_sub`: `‖P(x)‖ ≤ p^{L₀ + M₀}` when `v_p(x - r) ≥ L₀ + 1` and
  `x ≠ r`.
* `Zeta5Irr.neg_log_sub_max_le_addValuation_eval`: the main bound `v_p(P(x)) ≥ -L₀ - M₀`.

## Implementation notes

* The valuation is `Padic.addValuation`, valued in `ℤ ∪ {∞}`, so the case `P(x) = 0` is
  included. The intermediate estimates are stated for the norm, `‖y‖ = p^{-v_p(y)}`.
* `⌊log_p(2K)⌋` is `Nat.log p (2 * K)` and `⌊log_p max(1, d)⌋` is `Nat.log p (max 1 d)`.
* The source assumes `K ≥ 2`; the argument does not use it, and the hypothesis is omitted.
* The condition `v_p(x - s) ≥ L₀ + 1` is written `p ^ (L₀ + 1) ∣ x - s` in `ℤ_[p]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset Nat Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- If `-n ≤ v_p(y)` then `‖y‖ ≤ p^n` (also for `y = 0`). -/
theorem norm_le_zpow_of_neg_le_valuation {y : ℚ_[p]} {n : ℤ} (h : -n ≤ y.valuation) :
    ‖y‖ ≤ (p : ℝ) ^ n := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [norm_zero]; positivity
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hy, zpow_le_zpow_iff_right₀ hp]
  omega

/-- Since the norm on `ℚ_p` takes values in `p^ℤ ∪ {0}`, `p^{-(n+1)} < ‖y‖` implies
`‖y⁻¹‖ ≤ p^n`. -/
theorem norm_inv_le_zpow_of_zpow_lt_norm {y : ℚ_[p]} {n : ℤ}
    (h : (p : ℝ) ^ (-(n + 1)) < ‖y‖) : ‖y⁻¹‖ ≤ (p : ℝ) ^ n := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hy : y ≠ 0 :=
    norm_pos_iff.1 ((zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).trans h)
  rw [Padic.norm_eq_zpow_neg_valuation hy, zpow_lt_zpow_iff_right₀ hp] at h
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation hy, ← zpow_neg, neg_neg,
    zpow_le_zpow_iff_right₀ hp]
  omega

/-- If `p^n ∤ z` in `ℤ_p`, then `p^{-n} < ‖z‖`. -/
theorem zpow_lt_norm_of_not_pow_dvd {z : ℤ_[p]} {n : ℕ} (h : ¬ (p : ℤ_[p]) ^ n ∣ z) :
    (p : ℝ) ^ (-(n : ℤ)) < ‖(z : ℚ_[p])‖ := by
  by_contra h'
  rw [not_lt, ← PadicInt.norm_def, PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton] at h'
  exact h h'

variable {K : ℕ} {A P B : ℚ_[p][X]}

/-- **Partial fractions at a point.** If `(K!)² A = P E_{R_K} + B` with `deg B < 2K` and
`y ∉ R_K`, then `P(y) = (K!)² A(y) / E_{R_K}(y) - ∑_{s ∈ R_K} c_s / (y - s)`, where
`c_s = (K!)² A(s) / E_{R_K}'(s)`. -/
theorem eval_eq_div_sub_sum_of_eq_mul_add (hB : B.degree < ↑(2 * K))
    (hdiv : C ((K ! : ℚ_[p]) ^ 2) * A = P * intPoleProduct (puncturedIcc K) ℚ_[p] + B)
    {y : ℚ_[p]} (hy : ∀ s ∈ puncturedIcc K, y ≠ s) :
    P.eval y = (K ! : ℚ_[p]) ^ 2 * A.eval y / (intPoleProduct (puncturedIcc K) ℚ_[p]).eval y -
      ∑ s ∈ puncturedIcc K, (K ! : ℚ_[p]) ^ 2 * A.eval (s : ℚ_[p]) /
        (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (s : ℚ_[p]) / (y - s) := by
  have hpf := eq_mul_prod_add_sum_eval_div_derivative (v := fun s : ℤ ↦ (s : ℚ_[p]))
    (s := puncturedIcc K) Int.cast_injective.injOn hdiv (by rwa [card_puncturedIcc])
  have hys : ∀ s ∈ puncturedIcc K, y - s ≠ 0 := fun s hs ↦ sub_ne_zero.2 (hy s hs)
  have hE : (intPoleProduct (puncturedIcc K) ℚ_[p]).eval y ≠ 0 := by
    rw [eval_intPoleProduct]; exact prod_ne_zero_iff.2 hys
  have h1 : ∀ s ∈ puncturedIcc K, ∏ j ∈ (puncturedIcc K).erase s, (y - j) =
      (intPoleProduct (puncturedIcc K) ℚ_[p]).eval y / (y - s) := by
    intro s hs
    rw [eq_div_iff (hys s hs), mul_comm, mul_prod_erase _ (fun j : ℤ ↦ y - j) hs,
      eval_intPoleProduct]
  have hev := congrArg (eval y) hpf
  simp only [eval_add, eval_mul, eval_C, eval_finsetSum, eval_prod, eval_sub, eval_X] at hev
  rw [← intPoleProduct, ← eval_intPoleProduct,
    sum_congr rfl fun s hs ↦ by rw [h1 s hs]] at hev
  rw [eq_sub_iff_add_eq, eq_div_iff hE, hev, add_mul, sum_mul]
  congr 1
  exact sum_congr rfl fun s _ ↦ by ring

/-- If `A(ℤ_p) ⊆ ℤ_p`, `s ∈ R_K` and `v_p(y - s) ≤ ⌊log_p(2K)⌋`, then
`‖c_s / (y - s)‖ ≤ p^{2⌊log_p(2K)⌋}`, where `c_s = (K!)² A(s) / E_{R_K}'(s)`. -/
theorem norm_residue_div_sub_le (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) {s : ℤ}
    (hs : s ∈ puncturedIcc K) {y : ℚ_[p]}
    (hy : (p : ℝ) ^ (-((Nat.log p (2 * K) : ℤ) + 1)) < ‖y - s‖) :
    ‖(K ! : ℚ_[p]) ^ 2 * A.eval (s : ℚ_[p]) /
        (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (s : ℚ_[p]) / (y - s)‖ ≤
      (p : ℝ) ^ (2 * (Nat.log p (2 * K) : ℤ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [div_eq_mul_inv _ (y - s), norm_mul, two_mul, zpow_add₀ hp0.ne']
  gcongr
  · exact norm_le_zpow_of_neg_le_valuation (neg_log_le_valuation_factorial_sq_mul_eval_div hint hs)
  · exact norm_inv_le_zpow_of_zpow_lt_norm hy

/-- The case of `lem_small_poly_val` where `v_p(x - s) ≤ ⌊log_p(2K)⌋` for every `s ∈ R_K`:
then `‖P(x)‖ ≤ p^{2⌊log_p(2K)⌋}`. -/
theorem norm_eval_le_of_forall_not_pow_dvd (hB : B.degree < ↑(2 * K))
    (hdiv : C ((K ! : ℚ_[p]) ^ 2) * A = P * intPoleProduct (puncturedIcc K) ℚ_[p] + B)
    (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) {y : ℤ_[p]}
    (hy : ∀ s ∈ puncturedIcc K, ¬ (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ y - s) :
    ‖P.eval (y : ℚ_[p])‖ ≤ (p : ℝ) ^ (2 * (Nat.log p (2 * K) : ℤ)) := by
  have hlt : ∀ s ∈ puncturedIcc K,
      (p : ℝ) ^ (-((Nat.log p (2 * K) : ℤ) + 1)) < ‖(y : ℚ_[p]) - s‖ := by
    intro s hs
    have := zpow_lt_norm_of_not_pow_dvd (hy s hs)
    push_cast at this
    exact this
  have hne : ∀ s ∈ puncturedIcc K, (y : ℚ_[p]) ≠ s := fun s hs ↦
    sub_ne_zero.1 (norm_pos_iff.1 ((zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos)
      _).trans (hlt s hs)))
  rw [eval_eq_div_sub_sum_of_eq_mul_add hB hdiv hne, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine norm_le_zpow_of_neg_le_valuation ?_
    exact_mod_cast neg_two_log_le_valuation_factorial_sq_mul_eval_div (hint y) hy
  · rw [norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      fun s hs ↦ norm_residue_div_sub_le hint hs (hlt s hs)

/-- The case of `lem_small_poly_val` where `v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1` for some `r ∈ R_K`
with `x ≠ r`: then `‖P(x)‖ ≤ p^{L₀ + max(L₀, ⌊log_p d⌋)}` with `L₀ = ⌊log_p(2K)⌋`. -/
theorem norm_eval_le_of_pow_dvd_sub {d : ℕ} (hAd : A.natDegree ≤ d)
    (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) (hB : B.degree < ↑(2 * K))
    (hdiv : C ((K ! : ℚ_[p]) ^ 2) * A = P * intPoleProduct (puncturedIcc K) ℚ_[p] + B)
    {r : ℤ} (hr : r ∈ puncturedIcc K) {y : ℤ_[p]} (hyr : (y : ℚ_[p]) ≠ r)
    (hdvd : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ y - r) :
    ‖P.eval (y : ℚ_[p])‖ ≤
      (p : ℝ) ^ ((Nat.log p (2 * K) : ℤ) + max (Nat.log p (2 * K) : ℤ) (Nat.log p d)) := by
  set L : ℤ := ((Nat.log p (2 * K) : ℕ) : ℤ) with hL
  set M : ℤ := max L ((Nat.log p d : ℕ) : ℤ) with hM
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hQ := eval_poleDeletedDen_ne_zero_of_dvd hr hdvd
  rw [eval_intPoleProduct] at hQ
  have hQs : ∀ s ∈ (puncturedIcc K).erase r, (y : ℚ_[p]) - s ≠ 0 := prod_ne_zero_iff.1 hQ
  have hne : ∀ s ∈ puncturedIcc K, (y : ℚ_[p]) ≠ s := by
    intro s hs
    by_cases hsr : s = r
    · rw [hsr]; exact hyr
    · exact sub_ne_zero.1 (hQs s (mem_erase.2 ⟨hsr, hs⟩))
  have hyr0 : (y : ℚ_[p]) - r ≠ 0 := sub_ne_zero.2 hyr
  have hR0 : ∏ s ∈ (puncturedIcc K).erase r, ((r : ℚ_[p]) - s) ≠ 0 :=
    prod_ne_zero_iff.2 fun s hs ↦ sub_ne_zero.2 (by exact_mod_cast (ne_of_mem_erase hs).symm)
  have hEy : (intPoleProduct (puncturedIcc K) ℚ_[p]).eval (y : ℚ_[p]) =
      ((y : ℚ_[p]) - r) * ∏ s ∈ (puncturedIcc K).erase r, ((y : ℚ_[p]) - s) := by
    rw [eval_intPoleProduct, mul_prod_erase _ (fun s : ℤ ↦ (y : ℚ_[p]) - s) hr]
  have hE' : (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p]) =
      ∏ s ∈ (puncturedIcc K).erase r, ((r : ℚ_[p]) - s) := by
    rw [intPoleProduct, eval_derivative_prod_X_sub_C _ (fun s : ℤ ↦ (s : ℚ_[p])) hr]
  have hsplit : (K ! : ℚ_[p]) ^ 2 * A.eval (y : ℚ_[p]) /
        (intPoleProduct (puncturedIcc K) ℚ_[p]).eval (y : ℚ_[p]) -
      (K ! : ℚ_[p]) ^ 2 * A.eval (r : ℚ_[p]) /
        (derivative (intPoleProduct (puncturedIcc K) ℚ_[p])).eval (r : ℚ_[p]) /
        ((y : ℚ_[p]) - r) =
      (A.eval (y : ℚ_[p]) - A.eval (r : ℚ_[p])) * poleDeletedProductAt K r (y : ℚ_[p]) /
          ((y : ℚ_[p]) - r) +
        A.eval (r : ℚ_[p]) * (poleDeletedProductAt K r (y : ℚ_[p]) -
          poleDeletedProductAt K r (r : ℚ_[p])) / ((y : ℚ_[p]) - r) := by
    rw [hEy, hE']
    simp only [poleDeletedProductAt]
    field_simp
    ring
  rw [eval_eq_div_sub_sum_of_eq_mul_add hB hdiv hne, ← add_sum_erase _ _ hr, ← sub_sub, hsplit,
    sub_eq_add_neg]
  have hb : 0 ≤ (p : ℝ) ^ (L + M) := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
  · have hFy : ‖poleDeletedProductAt K r (y : ℚ_[p])‖ ≤ (p : ℝ) ^ L :=
      norm_le_zpow_of_neg_le_valuation (neg_log_le_valuation_poleDeletedProductAt hr hdvd)
    have hAd' := norm_eval_sub_eval_le hAd hint y r
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_intCast, ← zpow_natCast] at hAd'
    rw [norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.2 hyr0)]
    calc _ ≤ (p : ℝ) ^ (Nat.log p d : ℤ) * ‖(y : ℚ_[p]) - r‖ * (p : ℝ) ^ L := by gcongr
      _ ≤ (p : ℝ) ^ M * ‖(y : ℚ_[p]) - r‖ * (p : ℝ) ^ L := by
        gcongr
        · exact hp.le
        · exact le_max_right _ _
      _ = (p : ℝ) ^ (L + M) * ‖(y : ℚ_[p]) - r‖ := by rw [zpow_add₀ hp0.ne']; ring
  · have hz : y - (r : ℤ_[p]) ≠ 0 := by
      intro h
      apply hyr0
      rw [← PadicInt.coe_intCast, ← PadicInt.coe_sub, h, PadicInt.coe_zero]
    set n := (y - (r : ℤ_[p])).valuation
    have hn : (p : ℤ_[p]) ^ n ∣ y - r := (padicInt_pow_dvd_iff_le_valuation hz n).2 le_rfl
    have hnorm : ‖(y : ℚ_[p]) - r‖ = (p : ℝ) ^ (-(n : ℤ)) := by
      rw [← PadicInt.coe_intCast, ← PadicInt.coe_sub, ← PadicInt.norm_def,
        PadicInt.norm_eq_zpow_neg_valuation hz]
    have hF := intCast_le_padicAddValuation_iff.1
      (sub_two_log_le_addValuation_poleDeletedProductAt_sub hr hdvd hn)
    have hAr : ‖A.eval (r : ℚ_[p])‖ ≤ 1 := by simpa using hint r
    rw [norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.2 hyr0), hnorm]
    calc _ ≤ 1 * (p : ℝ) ^ (-((n : ℤ) - 2 * L)) := by gcongr
      _ = (p : ℝ) ^ (L + L) * (p : ℝ) ^ (-(n : ℤ)) := by
        rw [← zpow_add₀ hp0.ne', one_mul]; congr 1; ring
      _ ≤ (p : ℝ) ^ (L + M) * (p : ℝ) ^ (-(n : ℤ)) := by
        gcongr
        · exact hp.le
        · exact le_max_left _ _
  · rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb fun s hs ↦ ?_
    refine (norm_residue_div_sub_le hint (mem_of_mem_erase hs) ?_).trans ?_
    · rw [norm_sub_intCast_eq_of_mem_erase_puncturedIcc hr hdvd hs]
      exact zpow_lt_norm_intCast_sub hr hs
    · rw [two_mul]
      gcongr
      · exact hp.le
      · exact le_max_left _ _

/-- **The quotient polynomial at a small prime.** Let `p` be a prime and `A ∈ ℚ_p[x]` with
`deg A ≤ d` and `A(ℤ_p) ⊆ ℤ_p`, and let `(K!)² A = P E_{R_K} + B` with `deg B < 2K`. Then for
every `x ∈ ℤ_p`,
`v_p(P(x)) ≥ -⌊log_p(2K)⌋ - max(⌊log_p(2K)⌋, ⌊log_p max(1, d)⌋)`. -/
@[zeta5irr "lem_small_poly_val"]
theorem neg_log_sub_max_le_addValuation_eval {d : ℕ} (hAd : A.natDegree ≤ d)
    (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) (hB : B.degree < ↑(2 * K))
    (hdiv : C ((K ! : ℚ_[p]) ^ 2) * A = P * intPoleProduct (puncturedIcc K) ℚ_[p] + B)
    (x : ℤ_[p]) :
    ((-(Nat.log p (2 * K) : ℤ) - max (Nat.log p (2 * K) : ℤ) (Nat.log p (max 1 d)) : ℤ) :
        WithTop ℤ) ≤ Padic.addValuation (P.eval (x : ℚ_[p])) := by
  have hlog : Nat.log p (max 1 d) = Nat.log p d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [max_eq_right hd]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  set L : ℤ := ((Nat.log p (2 * K) : ℕ) : ℤ) with hL
  rw [hlog, intCast_le_padicAddValuation_iff, neg_sub, sub_neg_eq_add, add_comm]
  by_cases h : ∃ r ∈ puncturedIcc K, (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r
  · obtain ⟨r, hr, hdvd⟩ := h
    by_cases hxr : (x : ℚ_[p]) = r
    · rw [hxr]
      set y : ℕ → ℤ_[p] := fun n ↦ (r : ℤ_[p]) + (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) *
        (p : ℤ_[p]) ^ n with hy
      have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
      have hbound : ∀ n, ‖P.eval (y n : ℚ_[p])‖ ≤
          (p : ℝ) ^ (L + max L ((Nat.log p d : ℕ) : ℤ)) := fun n ↦
        norm_eval_le_of_pow_dvd_sub hAd hint hB hdiv hr (by simp [hy, hp0])
          (Dvd.intro ((p : ℤ_[p]) ^ n) (by simp [hy]))
      have ht : Tendsto (fun n ↦ (y n : ℚ_[p])) atTop (𝓝 (r : ℚ_[p])) := by
        have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one).const_mul
          ((p : ℚ_[p]) ^ (Nat.log p (2 * K) + 1))).const_add (r : ℚ_[p])
        simpa [hy] using this
      exact le_of_tendsto' ((P.continuous.tendsto _).comp ht).norm hbound
    · exact norm_eval_le_of_pow_dvd_sub hAd hint hB hdiv hr hxr hdvd
  · push Not at h
    exact (norm_eval_le_of_forall_not_pow_dvd hB hdiv hint h).trans
      (zpow_le_zpow_right₀ hp.le (by omega))

end Zeta5Irr
