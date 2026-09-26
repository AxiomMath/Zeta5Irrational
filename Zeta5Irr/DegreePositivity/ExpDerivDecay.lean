/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.ExpDerivForm
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exponential decay of the derivatives of `1 / (e^{2πy} - 1)`

For `0 ≤ k ≤ 4` and `y ≥ 1` the `k`-th derivative of `f(y) = 1 / (e^{2πy} - 1)` satisfies
`|f^{(k)}(y)| ≤ 10⁶ e^{-2πy}`.

With `q = e^{-2πy}` the closed form of the derivatives is
`f^{(k)}(y) = (-2π)^k q Φ_k(q) / (1 - q)^{k+1}`. For `y ≥ 1` one has
`0 < q ≤ e^{-6} < 1/100`, so `(1 - q)^{k+1} ≥ (99/100)^5 ≥ 1/2`; moreover `Φ_k(q) ≤ 24` and
`(2π)^k ≤ (2π)^4 < 7^4 = 2401`. Hence `|f^{(k)}(y)| ≤ 2401 · 24 · 2 · q < 10⁶ q`.

## Main results

* `Zeta5Irr.abs_iteratedDeriv_one_div_exp_sub_one_le_exp`: the bound
  `|f^{(k)}(y)| ≤ 10⁶ e^{-2πy}` for `k ≤ 4` and `y ≥ 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Real Polynomial

namespace Zeta5Irr

/-- For `0 ≤ k ≤ 4` and `y ≥ 1`, the `k`-th derivative of `1 / (e^{2πy} - 1)` is bounded in
absolute value by `10⁶ e^{-2πy}`. -/
@[zeta5irr "lem_w_f_decay"]
theorem abs_iteratedDeriv_one_div_exp_sub_one_le_exp {k : ℕ} (hk : k ≤ 4) {y : ℝ}
    (hy : 1 ≤ y) :
    |iteratedDeriv k (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y| ≤
      10 ^ 6 * Real.exp (-2 * π * y) := by
  rw [iteratedDeriv_one_div_exp_sub_one k (by linarith)]
  set q := Real.exp (-2 * π * y) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 / 100 := by
    have he : (100 : ℝ) ≤ Real.exp 6 := by
      rw [show Real.exp 6 = Real.exp 1 ^ 6 by rw [← Real.exp_nat_mul]; norm_num]
      calc (100 : ℝ) ≤ 2.7 ^ 6 := by norm_num
        _ ≤ Real.exp 1 ^ 6 :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 6
    calc q ≤ Real.exp (-6) := Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])
      _ = (Real.exp 6)⁻¹ := Real.exp_neg 6
      _ ≤ 1 / 100 := by rw [one_div]; exact inv_anti₀ (by norm_num) he
  have hΦ0 := aeval_derivNumerator_pos hk hq0.le
  have hΦ := aeval_derivNumerator_le hk hq0.le (by linarith : q ≤ 1)
  have hden : 1 / 2 ≤ (1 - q) ^ (k + 1) := by
    calc (1 / 2 : ℝ) ≤ (99 / 100) ^ 5 := by norm_num
      _ ≤ (1 - q) ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
      _ ≤ (1 - q) ^ (k + 1) :=
        pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hpi : (2 * π) ^ k ≤ 2401 := by
    calc (2 * π) ^ k ≤ (2 * π) ^ 4 := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hk
      _ ≤ 7 ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_d2]) 4
      _ = 2401 := by norm_num
  have hdpos : 0 < (1 - q) ^ (k + 1) := by linarith
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (mul_pos hq0 hΦ0), abs_of_pos hdpos,
    show |(-2 * π : ℝ)| = 2 * π by rw [abs_of_neg (by linarith [Real.pi_pos])]; ring,
    div_le_iff₀ hdpos]
  calc (2 * π) ^ k * (q * aeval q (derivNumerator k)) ≤ 2401 * (q * 24) :=
        mul_le_mul hpi (mul_le_mul_of_nonneg_left hΦ hq0.le) (by positivity) (by norm_num)
    _ ≤ 10 ^ 6 * q * (1 / 2) := by nlinarith
    _ ≤ 10 ^ 6 * q * (1 - q) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

end Zeta5Irr
