/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.ExpDerivForm
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A bound on the derivatives of `1 / (e^{2πy} - 1)` near the pole

For `0 ≤ k ≤ 4` and `0 < y ≤ 1` one has
`|(d/dy)^k 1 / (e^{2πy} - 1)| ≤ 10⁶ / y^{k+1}`.

With `q = e^{-2πy} ∈ (0, 1)` the closed form of the derivatives gives
`|(d/dy)^k 1 / (e^{2πy} - 1)| = (2π)^k q Φ_k(q) / (1 - q)^{k+1}`, where `Φ_k(q) ≤ 24` on
`[0, 1]`. Since `e^u ≥ 1 + u` with `u = 2πy ≤ 2π`, one has
`1 - q ≥ u / (1 + u) ≥ 2πy / (1 + 2π)`,
so the derivative is at most `24 (1 + 2π)^{k+1} / (2π y^{k+1}) ≤ 24 · 8⁵ / (6 y^{k+1})`.

## Main results

* `Zeta5Irr.abs_iteratedDeriv_one_div_exp_sub_one_le_div_pow`: the bound
  `|(d/dy)^k 1 / (e^{2πy} - 1)| ≤ 10⁶ / y^{k+1}` for `k ≤ 4` and `0 < y ≤ 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Real Polynomial

namespace Zeta5Irr

/-- **A bound on the derivatives of `1 / (e^{2πy} - 1)` near the pole.** For `k ≤ 4` and
`0 < y ≤ 1`, `|(d/dy)^k 1 / (e^{2πy} - 1)| ≤ 10⁶ / y^{k+1}`. -/
@[zeta5irr "lem_w_f_bound"]
theorem abs_iteratedDeriv_one_div_exp_sub_one_le_div_pow {k : ℕ} (hk : k ≤ 4) {y : ℝ}
    (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
    |iteratedDeriv k (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y| ≤ 10 ^ 6 / y ^ (k + 1) := by
  rw [iteratedDeriv_one_div_exp_sub_one k hy₀.ne']
  set q := Real.exp (-2 * π * y) with hq
  have hπ₃ := Real.pi_gt_three
  have hπ₄ := Real.pi_lt_d2
  have hq₀ : 0 < q := Real.exp_pos _
  have hu : 0 < 2 * π * y := by positivity
  have hq1 : q * (1 + 2 * π * y) ≤ 1 := by
    have h1 := Real.add_one_le_exp (2 * π * y)
    have h2 : q * Real.exp (2 * π * y) = 1 := by
      rw [hq, ← Real.exp_add, neg_mul, neg_mul, neg_add_cancel, Real.exp_zero]
    nlinarith
  have hq₁ : q ≤ 1 := by nlinarith
  have hc₀ : 0 < 2 * π * y / (1 + 2 * π) := by positivity
  have hc₁ : 2 * π * y / (1 + 2 * π) ≤ 1 - q := by
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ (1 - q) * (2 * π - 2 * π * y) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have hΦ₀ := aeval_derivNumerator_pos hk hq₀.le
  have hΦ₁ := aeval_derivNumerator_le hk hq₀.le hq₁
  have hkey : |(-2 * π) ^ k * (q * aeval q (derivNumerator k)) / (1 - q) ^ (k + 1)| ≤
      (2 * π) ^ k * 24 / (2 * π * y / (1 + 2 * π)) ^ (k + 1) := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : 0 < q * aeval q (derivNumerator k)),
      abs_of_pos (pow_pos (by linarith : 0 < 1 - q) (k + 1)),
      neg_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * π)]
    gcongr
    nlinarith
  refine hkey.trans ?_
  have hrw : (2 * π) ^ k * 24 / (2 * π * y / (1 + 2 * π)) ^ (k + 1) =
      24 * (1 + 2 * π) ^ (k + 1) / (2 * π) / y ^ (k + 1) := by
    have : (1 + 2 * π) ≠ 0 := by positivity
    rw [div_pow, mul_pow, pow_succ, pow_succ (1 + 2 * π)]
    field_simp
    ring
  rw [hrw]
  gcongr
  have h8 : (1 + 2 * π) ^ (k + 1) ≤ 8 ^ 5 :=
    (pow_le_pow_right₀ (by linarith) (by omega)).trans (pow_le_pow_left₀ (by positivity)
      (by linarith) 5)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Zeta5Irr
