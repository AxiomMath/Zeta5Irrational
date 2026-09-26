/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom
public import Zeta5Irr.LocalFunctional.SmallBinomVal
public import Zeta5Irr.LocalFunctional.SmallBinomInt
public import Zeta5Irr.LocalFunctional.SmallVandermonde
public import Zeta5Irr.LocalFunctional.SmallFrDiff
public import Mathlib.Algebra.Algebra.Field
public import Mathlib.Data.Rat.Star

/-!
# Divided derivatives of a `p`-adically bounded polynomial

Let `p` be a prime, `d, ρ ≥ 0`, `β ∈ ℤ`, and let `A ∈ ℚ_p[x]` have degree at most `d` with
`A(ℤ_p) ⊆ p^{-β} ℤ_p`. Then for every `x ∈ ℤ_p`,
`v_p(A^{(ρ)}(x) / ρ!) ≥ -β - ρ ⌊log_p max(1, d)⌋`.

Scaling by `p^β` and expanding in the binomial basis reduces the claim to `A = (x choose k)`
with `k ≤ d`. The divided derivative `(x choose k)^{(ρ)}(x) / ρ!` is the coefficient of `w^ρ`
in `(x + w choose k) = ∑_j (x choose j) (w choose k - j)`, and `(x choose j) ∈ ℤ_p`, so it
suffices to bound the coefficients of `(w choose m)` for `m ≤ d`. For `m ≥ 1`,
`(w choose m) = (w / m) ∏_{i=1}^{m-1} (w / i - 1)`, a product of polynomials whose coefficient of
`w^j` has norm at most `R^j` with `R = p^{⌊log_p max(1, d)⌋} ≥ ‖1 / i‖_p` for `1 ≤ i ≤ d`; this
weighted bound is preserved under products in an ultrametric field.

## Main results

* `Zeta5Irr.qbinom_succ_eq_prod`: `(x choose m + 1) = (x / (m + 1)) ∏_{i < m} (x / (i + 1) - 1)`.
* `Zeta5Irr.norm_natCast_inv_eq_zpow`: `‖1 / n‖_p = p^{v_p(n)}` for `n ≠ 0`.
* `Zeta5Irr.norm_coeff_map_qbinom_le`: `‖[x^j] (x choose m)‖_p ≤ p^{j ⌊log_p N⌋}` for `m ≤ N`.
* `Zeta5Irr.norm_eval_hasseDeriv_le`: the bound for the Hasse derivative `A^{(ρ)} / ρ!`.
* `Zeta5Irr.norm_eval_iterate_derivative_div_factorial_le`: the bound in norm form.
* `Zeta5Irr.neg_sub_le_addValuation_eval_iterate_derivative_div_factorial`: the bound in
  valuation form.

## Implementation notes

* The valuation is `Padic.addValuation`, valued in `ℤ ∪ {∞}`, so that the value `0` is allowed;
  the equivalent norm form `‖A^{(ρ)}(x) / ρ!‖_p ≤ p^{β + ρ ⌊log_p max(1, d)⌋}` is also given.
  The hypothesis `A(ℤ_p) ⊆ p^{-β} ℤ_p` is stated as `‖A(x)‖_p ≤ p^β` for `x ∈ ℤ_p`, and
  `⌊log_p max(1, d)⌋` is `Nat.log p (max 1 d)`.
* The source bounds the coefficients of `(w choose m)` by expanding the product into elementary
  symmetric functions of reciprocals; here the same estimate is obtained from the
  multiplicativity of the weighted bound `‖[w^j] P‖ ≤ R^j`
  (`Zeta5Irr.norm_coeff_mul_le_pow`), which avoids the explicit expansion.
* The divided derivative is Mathlib's Hasse derivative `Polynomial.hasseDeriv`, and Taylor's
  formula is `Polynomial.taylor_coeff`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Nat Finset

section Weighted

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {R : ℝ}

/-- In an ultrametric normed field, if the coefficients of `P` and `Q` satisfy
`‖[X^j] P‖ ≤ R^j` and `‖[X^j] Q‖ ≤ R^j`, then so do those of `P * Q`. -/
theorem norm_coeff_mul_le_pow (hR : 0 ≤ R) {P Q : K[X]} (hP : ∀ j, ‖P.coeff j‖ ≤ R ^ j)
    (hQ : ∀ j, ‖Q.coeff j‖ ≤ R ^ j) (n : ℕ) : ‖(P * Q).coeff n‖ ≤ R ^ n := by
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR n) ?_
  rintro ⟨i, j⟩ hij
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  dsimp only
  rw [norm_mul, ← hij, pow_add]
  exact mul_le_mul (hP i) (hQ j) (norm_nonneg _) (pow_nonneg hR _)

/-- In an ultrametric normed field, if the coefficients of each `P i` satisfy
`‖[X^j] P i‖ ≤ R^j`, then so do those of `∏ i ∈ s, P i`. -/
theorem norm_coeff_prod_le_pow {ι : Type*} (hR : 0 ≤ R) (s : Finset ι) {P : ι → K[X]}
    (hP : ∀ i ∈ s, ∀ j, ‖(P i).coeff j‖ ≤ R ^ j) (n : ℕ) :
    ‖(∏ i ∈ s, P i).coeff n‖ ≤ R ^ n := by
  revert n
  refine Finset.prod_induction _ (fun Q : K[X] => ∀ j, ‖Q.coeff j‖ ≤ R ^ j)
    (fun _ _ hA hB => norm_coeff_mul_le_pow hR hA hB) (fun j => ?_) hP
  rw [coeff_one]
  split_ifs with h
  · simp [h]
  · simpa using pow_nonneg hR j

end Weighted

/-- `(x choose m + 1) = (x choose m) (x - m) / (m + 1)`. -/
theorem qbinom_succ (m : ℕ) :
    qbinom (m + 1) = C ((m + 1 : ℚ))⁻¹ * qbinom m * (X - (m : ℚ[X])) := by
  rw [qbinom, qbinom, descPochhammer_succ_right, smul_eq_C_mul, smul_eq_C_mul, Nat.factorial_succ]
  push_cast
  rw [mul_inv, C_mul]
  ring

/-- `(x choose m + 1) = (x / (m + 1)) ∏_{i < m} (x / (i + 1) - 1)`. -/
theorem qbinom_succ_eq_prod (m : ℕ) :
    qbinom (m + 1) =
      C ((m + 1 : ℚ))⁻¹ * X * ∏ i ∈ range m, (C ((i + 1 : ℚ))⁻¹ * X - 1) := by
  induction m with
  | zero => simp [qbinom]
  | succ m ih =>
    have h : C ((m + 1 : ℚ))⁻¹ * (X - ((m + 1 : ℕ) : ℚ[X])) = C ((m + 1 : ℚ))⁻¹ * X - 1 := by
      rw [mul_sub, ← C_eq_natCast, ← C_mul]
      push_cast
      rw [inv_mul_cancel₀ (by positivity), C_1]
    rw [qbinom_succ, ih, prod_range_succ]
    push_cast at h ⊢
    linear_combination (C ((m + 1 + 1 : ℚ))⁻¹ * X *
      ∏ i ∈ range m, (C ((i + 1 : ℚ))⁻¹ * X - 1)) * h

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- For a nonzero natural number `n`, `‖1 / n‖_p = p^{v_p(n)}`. -/
theorem norm_natCast_inv_eq_zpow {n : ℕ} (hn : n ≠ 0) :
    ‖((n : ℚ_[p]))⁻¹‖ = (p : ℝ) ^ padicValNat p n := by
  have h0 : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, ← zpow_neg, neg_neg,
    zpow_natCast]

/-- For `1 ≤ n ≤ N`, `‖1 / n‖_p ≤ p^{⌊log_p N⌋}`. -/
theorem norm_algebraMap_inv_natCast_le {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    ‖algebraMap ℚ ℚ_[p] (n : ℚ)⁻¹‖ ≤ (p : ℝ) ^ Nat.log p N := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  rw [map_inv₀, map_natCast, norm_natCast_inv_eq_zpow (by omega)]
  exact pow_le_pow_right₀ hp ((padicValNat_le_nat_log n).trans (Nat.log_mono_right hN))

/-- For `1 ≤ n ≤ N`, the coefficients of `x / n - 1 ∈ ℚ_p[x]` satisfy
`‖[x^j] (x / n - 1)‖_p ≤ p^{j ⌊log_p N⌋}`. -/
theorem norm_coeff_C_inv_natCast_mul_X_sub_one_le {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) (j : ℕ) :
    ‖(C (algebraMap ℚ ℚ_[p] (n : ℚ)⁻¹) * X - 1).coeff j‖ ≤ ((p : ℝ) ^ Nat.log p N) ^ j := by
  have h := norm_algebraMap_inv_natCast_le (p := p) hn hN
  rcases j with _ | _ | j
  · simp
  · simpa [coeff_one] using h
  · simp only [coeff_sub, coeff_C_mul_X, coeff_one]
    simp

/-- The coefficients of `(x choose m)` satisfy `‖[x^j] (x choose m)‖_p ≤ p^{j ⌊log_p N⌋}`
whenever `m ≤ N`. -/
theorem norm_coeff_map_qbinom_le {m N : ℕ} (hm : m ≤ N) (j : ℕ) :
    ‖((qbinom m).map (algebraMap ℚ ℚ_[p])).coeff j‖ ≤ ((p : ℝ) ^ Nat.log p N) ^ j := by
  have hR : (0 : ℝ) ≤ (p : ℝ) ^ Nat.log p N := by positivity
  rcases m with _ | m
  · simpa using norm_coeff_prod_le_pow hR (∅ : Finset ℕ) (P := fun _ => (0 : ℚ_[p][X]))
      (by simp) j
  rw [qbinom_succ_eq_prod]
  simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, map_C, map_X,
    Polynomial.map_one]
  refine norm_coeff_mul_le_pow hR (fun i => ?_) (norm_coeff_prod_le_pow hR _ ?_) j
  · have h := norm_algebraMap_inv_natCast_le (p := p) (n := m + 1) (by omega) hm
    push_cast at h
    rw [coeff_C_mul_X]
    split_ifs with hi
    · simpa [hi] using h
    · simp
  · intro i hi j
    have := norm_coeff_C_inv_natCast_mul_X_sub_one_le (p := p) (n := i + 1) (N := N) (by omega)
      (by simp at hi; omega) j
    rwa [Nat.cast_succ] at this

/-- The divided derivatives of `(x choose m)` at `x ∈ ℤ_p` satisfy
`‖(x choose m)^{(ρ)}(x) / ρ!‖_p ≤ p^{ρ ⌊log_p N⌋}` whenever `m ≤ N`. -/
theorem norm_eval_hasseDeriv_map_qbinom_le {m N : ℕ} (hm : m ≤ N) (ρ : ℕ) (x : ℤ_[p]) :
    ‖(hasseDeriv ρ ((qbinom m).map (algebraMap ℚ ℚ_[p]))).eval (x : ℚ_[p])‖ ≤
      ((p : ℝ) ^ Nat.log p N) ^ ρ := by
  have hR : (0 : ℝ) ≤ (p : ℝ) ^ Nat.log p N := by positivity
  have hcomp : ∀ (q : ℚ[X]) (Y : ℚ_[p][X]), (q.map (algebraMap ℚ ℚ_[p])).comp Y = aeval Y q :=
    fun q Y => by rw [comp, eval₂_map, aeval_def]; rfl
  have hC : ∀ (q : ℚ[X]) (y : ℚ_[p]), aeval (C y : ℚ_[p][X]) q = C (aeval y q) :=
    fun q y => by rw [← algebraMap_eq, aeval_algebraMap_apply]
  rw [← taylor_coeff, taylor_apply, hcomp, add_comm, aeval_add_qbinom, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR ρ) fun j hj => ?_
  rw [hC, aeval_X_left_eq_map, coeff_C_mul, norm_mul]
  calc _ ≤ 1 * ((p : ℝ) ^ Nat.log p N) ^ ρ :=
        mul_le_mul (norm_aeval_qbinom_le_one j x) (norm_coeff_map_qbinom_le (by omega) ρ)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Divided derivatives of a `p`-adically bounded polynomial**, in the Hasse-derivative form.
If `A ∈ ℚ_p[x]` has degree at most `d` and `A(ℤ_p) ⊆ p^{-β} ℤ_p`, then
`‖A^{[ρ]}(x)‖_p ≤ p^{β + ρ ⌊log_p max(1, d)⌋}` for every `x ∈ ℤ_p`, where `A^{[ρ]}` is the
`ρ`-th Hasse derivative `A^{(ρ)} / ρ!`. -/
theorem norm_eval_hasseDeriv_le {d : ℕ} (ρ : ℕ) {β : ℤ} {A : ℚ_[p][X]} (hA : A.natDegree ≤ d)
    (hbd : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ (p : ℝ) ^ β) (x : ℤ_[p]) :
    ‖(hasseDeriv ρ A).eval (x : ℚ_[p])‖ ≤ (p : ℝ) ^ (β + ρ * Nat.log p (max 1 d)) := by
  set L := Nat.log p (max 1 d)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hR : (0 : ℝ) ≤ (p : ℝ) ^ L := by positivity
  set c : ℚ_[p] := (p : ℚ_[p]) ^ β
  have hc : ‖c‖ = (p : ℝ) ^ (-β) := by rw [norm_zpow, Padic.norm_p, inv_zpow']
  have hc0 : c ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_qbinom (A := c • A) (d := d)
    ((natDegree_smul_le _ _).trans hA) fun y => by
      rw [eval_smul, smul_eq_mul, norm_mul, hc]
      calc _ ≤ (p : ℝ) ^ (-β) * (p : ℝ) ^ β := by gcongr; exact hbd y
        _ = 1 := by rw [← zpow_add₀ hp0.ne', neg_add_cancel, zpow_zero]
  have hA' : A = c⁻¹ • c • A := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hexp : (p : ℝ) ^ (β + ρ * L) = (p : ℝ) ^ β * ((p : ℝ) ^ L) ^ ρ := by
    rw [zpow_add₀ hp0.ne', ← pow_mul, ← zpow_natCast]
    push_cast
    ring_nf
  rw [hA', ha, map_smul, map_sum, eval_smul, eval_finsetSum, smul_eq_mul, norm_mul, norm_inv, hc,
    ← zpow_neg, neg_neg, hexp]
  gcongr
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR ρ) fun k hk => ?_
  rw [map_smul, eval_smul, smul_eq_mul, norm_mul]
  have hk' : k ≤ max 1 d := (Nat.lt_succ_iff.mp (mem_range.mp hk)).trans (le_max_right _ _)
  calc _ ≤ 1 * ((p : ℝ) ^ L) ^ ρ :=
        mul_le_mul (a k).norm_le_one (norm_eval_hasseDeriv_map_qbinom_le hk' ρ x)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Divided derivatives of a `p`-adically bounded polynomial.** If `A ∈ ℚ_p[x]` has degree at
most `d` and `A(ℤ_p) ⊆ p^{-β} ℤ_p`, then `‖A^{(ρ)}(x) / ρ!‖_p ≤ p^{β + ρ ⌊log_p max(1, d)⌋}`
for every `x ∈ ℤ_p`. -/
theorem norm_eval_iterate_derivative_div_factorial_le {d : ℕ} (ρ : ℕ) {β : ℤ} {A : ℚ_[p][X]}
    (hA : A.natDegree ≤ d) (hbd : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ (p : ℝ) ^ β)
    (x : ℤ_[p]) :
    ‖(derivative^[ρ] A).eval (x : ℚ_[p]) / (ρ ! : ℚ_[p])‖ ≤
      (p : ℝ) ^ (β + ρ * Nat.log p (max 1 d)) := by
  have h : derivative^[ρ] A = (ρ ! : ℚ_[p]) • hasseDeriv ρ A := by
    rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  rw [h, eval_smul, smul_eq_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr ρ.factorial_ne_zero)]
  exact norm_eval_hasseDeriv_le ρ hA hbd x

/-- **Divided derivatives of a `p`-adically bounded polynomial**, in valuation form. Let `p` be a
prime, `d, ρ ≥ 0`, `β ∈ ℤ`, and let `A ∈ ℚ_p[x]` have degree at most `d` with
`A(ℤ_p) ⊆ p^{-β} ℤ_p`. Then for every `x ∈ ℤ_p`,
`v_p(A^{(ρ)}(x) / ρ!) ≥ -β - ρ ⌊log_p max(1, d)⌋`. -/
@[zeta5irr "lem_small_deriv"]
theorem neg_sub_le_addValuation_eval_iterate_derivative_div_factorial {d : ℕ} (ρ : ℕ) {β : ℤ}
    {A : ℚ_[p][X]} (hA : A.natDegree ≤ d)
    (hbd : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ (p : ℝ) ^ β) (x : ℤ_[p]) :
    ((-β - ρ * Nat.log p (max 1 d) : ℤ) : WithTop ℤ) ≤
      Padic.addValuation ((derivative^[ρ] A).eval (x : ℚ_[p]) / (ρ ! : ℚ_[p])) := by
  rw [intCast_le_padicAddValuation_iff, neg_sub, sub_neg_eq_add, add_comm]
  exact norm_eval_iterate_derivative_div_factorial_le ρ hA hbd x

end Padic

end Zeta5Irr
