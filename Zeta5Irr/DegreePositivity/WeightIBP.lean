/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.Kernel
public import Zeta5Irr.DegreePositivity.WeightDeriv
public import Zeta5Irr.DegreePositivity.ExpDerivBound
public import Zeta5Irr.DegreePositivity.ExpDerivDecay
public import Zeta5Irr.DegreePositivity.KernelPrimitiveBoundary
public import Zeta5Irr.DegreePositivity.KernelDeriv
public import Zeta5Irr.DegreePositivity.KernelPrimitiveGrowth
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Integrating the weight against `1 / (y² + b²)` by parts

Write `f(y) = 1 / (e^{2πy} - 1)` and `g(y) = y⁵ / (y² + b²)`. Since `w(y) = y⁵ f⁽⁴⁾(y) / 12`,
the integrand `w(y) / (y² + b²)` is `g(y) f⁽⁴⁾(y) / 12`. Four integrations by parts on
`(0, ∞)` move the four derivatives from `f` to `g`, and `g⁽⁴⁾ = 24 b⁴ Ψ_b`, so
`∫₀^∞ w(y) / (y² + b²) dy = 2 b⁴ ∫₀^∞ Ψ_b(y) / (e^{2πy} - 1) dy`.

Every product `g⁽ᵐ⁾ f⁽ʲ⁾` with `j + m ≤ 4` is integrable on `(0, ∞)`: near `0` the pole of
order `j + 1` of `f⁽ʲ⁾` is cancelled by the zero of order `5 - m` of `g⁽ᵐ⁾`, and near `∞` the
factor `e^{-2πy}` in `f⁽ʲ⁾` beats the growth of `g⁽ᵐ⁾`. When `j + m ≤ 3` the product moreover
tends to `0` at both ends, so no boundary terms appear.

## Main results

* `Zeta5Irr.integral_weight_div_sq_add_sq`:
  `∫₀^∞ w(y) / (y² + b²) dy = 2 b⁴ ∫₀^∞ Ψ_b(y) / (e^{2πy} - 1) dy` for `b ≠ 0`.

## Implementation notes

The source states the identity for `b > 0`; it holds, with the same proof, for every `b ≠ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (expanding the exponential factor).
-/

@[expose] public section

namespace Zeta5Irr

open Real Set Filter Topology MeasureTheory Asymptotics
open scoped ContDiff

/-- The derivatives of `1 / (e^{2πy} - 1)` are smooth on `(0, ∞)`. -/
theorem contDiffOn_iteratedDeriv_one_div_exp_sub_one (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv k fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) (Ioi 0) := by
  induction k with
  | zero =>
    rw [iteratedDeriv_zero]
    refine contDiffOn_const.div ((Real.contDiff_exp.comp
      (contDiff_const.mul contDiff_id)).sub contDiff_const).contDiffOn fun y (hy : 0 < y) => ?_
    exact (sub_pos.2 (Real.one_lt_exp_iff.2 (by positivity))).ne'
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

/-- On `(0, ∞)`, the `k`-th derivative of `1 / (e^{2πy} - 1)` has the `(k + 1)`-st as its
derivative. -/
theorem hasDerivAt_iteratedDeriv_one_div_exp_sub_one (k : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (iteratedDeriv k fun y ↦ 1 / (Real.exp (2 * π * y) - 1))
      (iteratedDeriv (k + 1) (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) y := by
  rw [iteratedDeriv_succ]
  have hd := (contDiffOn_iteratedDeriv_one_div_exp_sub_one k).differentiableOn (by simp)
  exact ((hd y hy).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt

/-- For `b ≠ 0`, the function `y ↦ y⁵ / (y² + b²)` is smooth. -/
theorem contDiff_pow_five_div_sq_add_sq {b : ℝ} (hb : b ≠ 0) :
    ContDiff ℝ ∞ fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2) :=
  (contDiff_id.pow 5).div ((contDiff_id.pow 2).add contDiff_const) fun y => by positivity

/-- For `b ≠ 0`, the `m`-th derivative of `y ↦ y⁵ / (y² + b²)` has the `(m + 1)`-st as its
derivative. -/
theorem hasDerivAt_iteratedDeriv_pow_five_div_sq_add_sq {b : ℝ} (hb : b ≠ 0) (m : ℕ) (y : ℝ) :
    HasDerivAt (iteratedDeriv m fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2))
      (iteratedDeriv (m + 1) (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y) y := by
  rw [iteratedDeriv_succ]
  exact (((contDiff_pow_five_div_sq_add_sq hb).differentiable_iteratedDeriv m
    (mod_cast ENat.natCast_lt_top m)).differentiableAt).hasDerivAt

/-- Near the origin, `g⁽ᵐ⁾(y) f⁽ʲ⁾(y) = O(y^{4 - j - m})` for `j + m ≤ 4`, where
`f(y) = 1 / (e^{2πy} - 1)` and `g(y) = y⁵ / (y² + b²)`. -/
theorem exists_abs_iteratedDeriv_mul_iteratedDeriv_le {b : ℝ} (hb : b ≠ 0) {j m : ℕ}
    (hjm : j + m ≤ 4) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ Ioc (0 : ℝ) 1,
      |iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
        iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y| ≤
        C * y ^ (4 - (j + m)) := by
  obtain ⟨C, hC⟩ := exists_bound_zpow_mul_iteratedDeriv_kernelPrimitive hb (m := m) (by omega)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1 ⟨one_pos, le_rfl⟩)
  refine ⟨C * 10 ^ 6, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := hy.1
  have h1 := hC y hy
  have h2 := abs_iteratedDeriv_one_div_exp_sub_one_le_div_pow (k := j) (by omega) hy.1 hy.2
  set G := iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y
  set F := iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y
  have hG : G = y ^ (5 - m) * (y ^ ((m : ℤ) - 5) * G) := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hy0.ne']
    push_cast [show m ≤ 5 by omega]
    simp
  have hF : |F| * y ^ (j + 1) ≤ 10 ^ 6 := by rwa [le_div_iff₀ (by positivity)] at h2
  have hpow : y ^ (5 - m) = y ^ (4 - (j + m)) * y ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hG, hpow, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < y ^ (4 - (j + m)) * y ^ (j + 1))]
  calc y ^ (4 - (j + m)) * y ^ (j + 1) * |y ^ ((m : ℤ) - 5) * G| * |F|
      = y ^ (4 - (j + m)) * |y ^ ((m : ℤ) - 5) * G| * (|F| * y ^ (j + 1)) := by ring
    _ ≤ y ^ (4 - (j + m)) * C * 10 ^ 6 := by gcongr
    _ = C * 10 ^ 6 * y ^ (4 - (j + m)) := by ring

/-- At infinity, `g⁽ᵐ⁾(y) f⁽ʲ⁾(y) = O(e^{-πy})` for `j ≤ 4`, where `f(y) = 1 / (e^{2πy} - 1)`
and `g(y) = y⁵ / (y² + b²)`. -/
theorem isBigO_iteratedDeriv_mul_iteratedDeriv {b : ℝ} (hb : b ≠ 0) {j : ℕ} (hj : j ≤ 4)
    (m : ℕ) :
    (fun y => iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
        iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) =O[atTop]
      fun y => Real.exp (-π * y) := by
  have ha := (tendsto_exp_neg_mul_iteratedDeriv_kernelPrimitive hb m).isBigO_one ℝ
  have hc : (fun y => Real.exp (π * y) *
      iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) =O[atTop]
        fun y => Real.exp (-π * y) := by
    refine IsBigO.of_bound (10 ^ 6) ?_
    filter_upwards [eventually_ge_atTop 1] with y hy
    have hF := abs_iteratedDeriv_one_div_exp_sub_one_le_exp hj hy
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    calc Real.exp (π * y) * |iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y|
        ≤ Real.exp (π * y) * (10 ^ 6 * Real.exp (-2 * π * y)) := by gcongr
      _ = 10 ^ 6 * Real.exp (-π * y) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf
  refine (ha.mul hc).congr (fun y => ?_) (fun y => one_mul _)
  rw [mul_mul_mul_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- For `j + m ≤ 4`, the product `g⁽ᵐ⁾ f⁽ʲ⁾` is integrable on `(0, ∞)`, where
`f(y) = 1 / (e^{2πy} - 1)` and `g(y) = y⁵ / (y² + b²)`. -/
theorem integrableOn_iteratedDeriv_mul_iteratedDeriv {b : ℝ} (hb : b ≠ 0) {j m : ℕ}
    (hjm : j + m ≤ 4) :
    IntegrableOn (fun y => iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
      iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) (Ioi 0) := by
  have hcont : ContinuousOn (fun y => iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
      iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) (Ioi 0) :=
    ((contDiff_pow_five_div_sq_add_sq hb).continuous_iteratedDeriv m
      (mod_cast (ENat.natCast_lt_top m).le)).continuousOn.mul
      (contDiffOn_iteratedDeriv_one_div_exp_sub_one j).continuousOn
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · obtain ⟨C, hC0, hC⟩ := exists_abs_iteratedDeriv_mul_iteratedDeriv_le hb hjm
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) C ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs]
    exact (hC y hy).trans (mul_le_of_le_one_right hC0 (pow_le_one₀ hy.1.le hy.2))
  · exact integrable_of_isBigO_exp_neg pi_pos
      (hcont.mono fun y (hy : 1 ≤ y) => lt_of_lt_of_le one_pos hy)
      (isBigO_iteratedDeriv_mul_iteratedDeriv hb (by omega) m)

/-- For `j + m ≤ 3`, the product `g⁽ᵐ⁾ f⁽ʲ⁾` tends to `0` at `0⁺`, where
`f(y) = 1 / (e^{2πy} - 1)` and `g(y) = y⁵ / (y² + b²)`. -/
theorem tendsto_iteratedDeriv_mul_iteratedDeriv_nhdsGT_zero {b : ℝ} (hb : b ≠ 0) {j m : ℕ}
    (hjm : j + m ≤ 3) :
    Tendsto (fun y => iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
      iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := exists_abs_iteratedDeriv_mul_iteratedDeriv_le hb (by omega : j + m ≤ 4)
  refine squeeze_zero_norm' (a := fun y => C * y ^ (4 - (j + m))) ?_ ?_
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with y hy
    rw [Real.norm_eq_abs]
    exact hC y hy
  · have h : Tendsto (fun y : ℝ => C * y ^ (4 - (j + m))) (𝓝 0) (𝓝 (C * 0 ^ (4 - (j + m)))) :=
      (continuous_const.mul (continuous_pow _)).tendsto 0
    rw [zero_pow (by omega), mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds

/-- For `j ≤ 4`, the product `g⁽ᵐ⁾ f⁽ʲ⁾` tends to `0` at infinity, where
`f(y) = 1 / (e^{2πy} - 1)` and `g(y) = y⁵ / (y² + b²)`. -/
theorem tendsto_iteratedDeriv_mul_iteratedDeriv_atTop {b : ℝ} (hb : b ≠ 0) {j : ℕ} (hj : j ≤ 4)
    (m : ℕ) :
    Tendsto (fun y => iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
      iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y) atTop (𝓝 0) := by
  refine (isBigO_iteratedDeriv_mul_iteratedDeriv hb hj m).trans_tendsto ?_
  have : Tendsto (fun y : ℝ => -π * y) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos pi_pos)
  exact Real.tendsto_exp_atBot.comp this

/-- **One integration by parts.** For `j + m ≤ 3`,
`∫₀^∞ g⁽ᵐ⁾ f⁽ʲ⁺¹⁾ = -∫₀^∞ g⁽ᵐ⁺¹⁾ f⁽ʲ⁾`, where `f(y) = 1 / (e^{2πy} - 1)` and
`g(y) = y⁵ / (y² + b²)`. -/
theorem integral_iteratedDeriv_mul_iteratedDeriv_succ {b : ℝ} (hb : b ≠ 0) {j m : ℕ}
    (hjm : j + m ≤ 3) :
    ∫ y in Ioi 0, iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
        iteratedDeriv (j + 1) (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y =
      -∫ y in Ioi 0, iteratedDeriv (m + 1) (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
        iteratedDeriv j (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (fun y _ => hasDerivAt_iteratedDeriv_pow_five_div_sq_add_sq hb m y)
    (fun y hy => hasDerivAt_iteratedDeriv_one_div_exp_sub_one j hy)
    (integrableOn_iteratedDeriv_mul_iteratedDeriv hb (by omega))
    (integrableOn_iteratedDeriv_mul_iteratedDeriv hb (by omega))
    (tendsto_iteratedDeriv_mul_iteratedDeriv_nhdsGT_zero hb hjm)
    (tendsto_iteratedDeriv_mul_iteratedDeriv_atTop hb (by omega) m)

/-- **Integration by parts against the weight.** For real `b ≠ 0`,
`∫₀^∞ w(y) / (y² + b²) dy = 2 b⁴ ∫₀^∞ Ψ_b(y) / (e^{2πy} - 1) dy`. -/
@[zeta5irr "lem_w_ibp"]
theorem integral_weight_div_sq_add_sq {b : ℝ} (hb : b ≠ 0) :
    ∫ y in Ioi 0, weight y / (y ^ 2 + b ^ 2) =
      2 * b ^ 4 * ∫ y in Ioi 0, weightKernel b y / (Real.exp (2 * π * y) - 1) := by
  have h0 : ∫ y in Ioi 0, weight y / (y ^ 2 + b ^ 2) =
      1 / 12 * ∫ y in Ioi 0, iteratedDeriv 0 (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
        iteratedDeriv (3 + 1) (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
    rw [iteratedDeriv_zero, weight_eq_iteratedDeriv hy]
    have : y ^ 2 + b ^ 2 ≠ 0 := by positivity
    field_simp
  have h4 : ∫ y in Ioi 0, iteratedDeriv (3 + 1) (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y *
        iteratedDeriv 0 (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y =
      24 * b ^ 4 * ∫ y in Ioi 0, weightKernel b y / (Real.exp (2 * π * y) - 1) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [iteratedDeriv_four_pow_five_div_sq_add_sq hb, iteratedDeriv_zero]
    ring
  rw [h0, integral_iteratedDeriv_mul_iteratedDeriv_succ hb (j := 3) (m := 0) (by norm_num),
    integral_iteratedDeriv_mul_iteratedDeriv_succ hb (j := 2) (m := 0 + 1) (by norm_num),
    integral_iteratedDeriv_mul_iteratedDeriv_succ hb (j := 1) (m := 0 + 1 + 1) (by norm_num),
    integral_iteratedDeriv_mul_iteratedDeriv_succ hb (j := 0) (m := 0 + 1 + 1 + 1) (by norm_num),
    h4]
  ring

end Zeta5Irr
