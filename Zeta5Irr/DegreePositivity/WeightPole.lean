/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.WeightIBP
public import Zeta5Irr.DegreePositivity.ExpPartialFractions
public import Zeta5Irr.DegreePositivity.KernelIntegrableRecip
public import Zeta5Irr.DegreePositivity.KernelIntegral
public import Zeta5Irr.DegreePositivity.KernelRecipIntegral
public import Zeta5Irr.DegreePositivity.KernelMoment
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Parameters.PoleValue

/-!
# The weight against a simple pole

For every integer `j ≥ 1`, `∫_0^∞ w(y) / (y² + j²) dy = ν_j(ξ)`.

Integrating by parts four times turns the left side into
`2 j⁴ ∫_0^∞ Ψ_j(y) / (e^{2πy} - 1) dy`. The partial fraction expansion
`1 / (e^{2πy} - 1) = -1/2 + 1/(2πy) + (1/π) ∑_{v ≥ 1} y / (y² + v²)` splits the integrand into
three pieces. The series may be integrated term by term, since
`∑_{v ≥ 1} y / (y² + v²) ≤ (1 + π) / 2` and `Ψ_j` is integrable. The three pieces integrate
to `1 / (4 j⁴)`, `π / (2 j⁵)` and `π / (2 (v + j)⁵)`, and the resulting tail
`∑_{v ≥ 1} (v + j)⁻⁵` is `ξ - H_j^{(5)}`.

## Main results

* `Zeta5Irr.tsum_div_sq_add_succ_sq_le`: `∑_{v ≥ 1} y / (y² + v²) ≤ (1 + π) / 2` for `y > 0`.
* `Zeta5Irr.integral_weightKernel_div_exp_sub_one`: for `b > 0`,
  `∫_0^∞ Ψ_b(y) / (e^{2πy} - 1) dy = -1 / (8 b⁴) + 1 / (4 b⁵) + (1/2) ∑_{v ≥ 1} (v + b)⁻⁵`.
* `Zeta5Irr.tsum_inv_add_succ_pow_five`: `∑_{v ≥ 1} (v + j)⁻⁵ = ξ - H_j^{(5)}`.
* `Zeta5Irr.integral_weight_div_sq_add_natCast_sq`: `∫_0^∞ w(y) / (y² + j²) dy = ν_j(ξ)`.

## Implementation notes

Sums over `v ≥ 1` are written as sums over `v : ℕ` of the term at `v + 1`. The interchange of
sum and integral is `MeasureTheory.integral_tsum`, whose hypothesis (finiteness of
`∑_v ∫ ‖f_v‖`) is checked by the monotone convergence theorem `MeasureTheory.lintegral_tsum`,
as in the source. The evaluation of the kernel integral holds for every real `b > 0`; only the
identification of the tail with `ξ - H_j^{(5)}` uses that `j` is an integer.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Real Set Polynomial

namespace Zeta5Irr

/-- For `y > 0`, `∑_{v ≥ 1} y / (y² + v²) ≤ (1 + π) / 2`. -/
theorem tsum_div_sq_add_succ_sq_le {y : ℝ} (hy : 0 < y) :
    ∑' v : ℕ, y / (y ^ 2 + ((v : ℝ) + 1) ^ 2) ≤ (1 + π) / 2 := by
  refine Real.tsum_le_of_sum_range_le (fun v => by positivity) fun n => ?_
  have h := (sum_Icc_one_eq_sum_range (fun v : ℕ => y / (y ^ 2 + (v : ℝ) ^ 2)) n).symm
  push_cast at h
  exact h ▸ sum_div_sq_add_sq_le hy n

/-- For `b > 0`, `∫_0^∞ Ψ_b(y) / (e^{2πy} - 1) dy
= -1 / (8 b⁴) + 1 / (4 b⁵) + (1/2) ∑_{v ≥ 1} (v + b)⁻⁵`. -/
theorem integral_weightKernel_div_exp_sub_one {b : ℝ} (hb : 0 < b) :
    ∫ y in Ioi 0, weightKernel b y / (Real.exp (2 * π * y) - 1) =
      -1 / (8 * b ^ 4) + 1 / (4 * b ^ 5) + 1 / 2 * ∑' v : ℕ, 1 / ((v : ℝ) + 1 + b) ^ 5 := by
  set g : ℕ → ℝ → ℝ := fun v y => y / (y ^ 2 + ((v : ℝ) + 1) ^ 2) * weightKernel b y with hg
  have hK := integrableOn_weightKernel_Ioi hb.ne'
  have hKc := continuous_weightKernel hb.ne'
  have hgc : ∀ v, Continuous (g v) := fun v =>
    (continuous_id.div (by fun_prop) fun y => by positivity).mul hKc
  -- pointwise, the series of norms is `T(y) |Ψ_b(y)|` with `T(y) ≤ (1 + π) / 2`
  have hsum : ∀ y : ℝ, 0 < y → Summable fun v : ℕ => y / (y ^ 2 + ((v : ℝ) + 1) ^ 2) :=
    fun y hy => (hasSum_div_sq_add_succ_sq hy).summable
  have hnorm : ∀ y : ℝ, 0 < y → ∀ v, ‖g v y‖ = y / (y ^ 2 + ((v : ℝ) + 1) ^ 2) * |weightKernel b y|
      := fun y hy v => by
    rw [hg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have hbound : ∀ y ∈ Ioi (0 : ℝ), ‖∑' v, g v y‖ ≤ (1 + π) / 2 * ‖weightKernel b y‖ := by
    intro y (hy : 0 < y)
    rw [hg, tsum_mul_right, norm_mul, Real.norm_of_nonneg (tsum_nonneg fun v => by positivity)]
    exact mul_le_mul_of_nonneg_right (tsum_div_sq_add_succ_sq_le hy) (norm_nonneg _)
  have hfin : ∑' v, ∫⁻ y in Ioi 0, ‖g v y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun v => (hgc v).aestronglyMeasurable.enorm]
    refine (lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun y (hy : 0 < y) => ?_)
      ((hK.const_mul ((1 + π) / 2)).hasFiniteIntegral)).ne
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => norm_nonneg _)
      (by simpa [hnorm y hy] using (hsum y hy).mul_right |weightKernel b y|)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp_rw [hnorm y hy, tsum_mul_right, norm_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1 + π) / 2)]
    exact mul_le_mul_of_nonneg_right (tsum_div_sq_add_succ_sq_le hy) (abs_nonneg _)
  have hS : ∫ y in Ioi 0, ∑' v, g v y = ∑' v : ℕ, π / (2 * ((v : ℝ) + 1 + b) ^ 5) := by
    rw [integral_tsum (fun v => (hgc v).aestronglyMeasurable) hfin]
    exact tsum_congr fun v =>
      integral_Ioi_div_sq_add_sq_mul_weightKernel (by positivity : (0 : ℝ) < v + 1) hb
  have hSi : IntegrableOn (fun y => ∑' v, g v y) (Ioi 0) := by
    refine (hK.norm.const_mul ((1 + π) / 2)).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound))
    refine ContinuousOn.aestronglyMeasurable (f := fun y => (π / (Real.exp (2 * π * y) - 1) +
      π / 2 - 1 / (2 * y)) * weightKernel b y) ?_ measurableSet_Ioi |>.congr ?_
    · refine ContinuousOn.mul ?_ hKc.continuousOn
      refine ((continuousOn_const.div (by fun_prop) fun y (hy : 0 < y) => ?_).add
        continuousOn_const).sub (continuousOn_const.div (by fun_prop) fun y (hy : 0 < y) => ?_)
      · exact (sub_pos.2 (Real.one_lt_exp_iff.2 (by positivity))).ne'
      · positivity
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
        fun y (hy : 0 < y) => ?_)
      simp only [hg, tsum_mul_right, (hasSum_div_sq_add_succ_sq hy).tsum_eq]
  have hpt : ∀ y ∈ Ioi (0 : ℝ), weightKernel b y / (Real.exp (2 * π * y) - 1) =
      -1 / 2 * weightKernel b y + 1 / (2 * π) * (weightKernel b y / y) +
        1 / π * ∑' v, g v y := by
    intro y (hy : 0 < y)
    rw [div_eq_mul_one_div, one_div_exp_sub_one_eq hy, hg]
    simp only [tsum_mul_right]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_weightKernel_Ioi hb.ne',
    integral_weightKernel_div_self hb, hS, tsum_mul_left.symm]
  · rw [← tsum_mul_left]
    have : ∀ v : ℕ, 1 / π * (π / (2 * ((v : ℝ) + 1 + b) ^ 5)) =
        1 / 2 * (1 / ((v : ℝ) + 1 + b) ^ 5) := fun v => by
      field_simp
    simp_rw [this]
    field_simp
    ring
  · exact hK.const_mul _
  · exact (integrableOn_weightKernel_div_self hb.ne').const_mul _
  · exact (hK.const_mul _).add ((integrableOn_weightKernel_div_self hb.ne').const_mul _)
  · exact hSi.const_mul _

/-- For `j : ℕ`, `∑_{v ≥ 1} (v + j)⁻⁵ = ξ - H_j^{(5)}`. -/
theorem tsum_inv_add_succ_pow_five (j : ℕ) :
    ∑' v : ℕ, 1 / ((v : ℝ) + 1 + j) ^ 5 = zetaFive - harmonicFive j := by
  have hs : Summable fun v : ℕ => ((v : ℝ) ^ 5)⁻¹ := Real.summable_nat_pow_inv.2 (by norm_num)
  have h := hs.sum_add_tsum_nat_add (j + 1)
  rw [zetaFive_eq_tsum_inv, ← h, Finset.sum_range_succ', harmonicFive,
    sum_Icc_one_eq_sum_range]
  push_cast
  simp only [one_div, add_assoc, add_comm (1 : ℝ) j]
  simp

/-- **The weight against a simple pole.** For every integer `j ≥ 1`,
`∫_0^∞ w(y) / (y² + j²) dy = ν_j(ξ)`. -/
@[zeta5irr "lem_w_pole"]
theorem integral_weight_div_sq_add_natCast_sq {j : ℕ} (hj : j ≠ 0) :
    ∫ y in Ioi 0, weight y / (y ^ 2 + (j : ℝ) ^ 2) = aeval zetaFive (poleValue j) := by
  have hj' : (0 : ℝ) < j := by positivity
  rw [integral_weight_div_sq_add_sq hj'.ne', integral_weightKernel_div_exp_sub_one hj',
    tsum_inv_add_succ_pow_five, aeval_poleValue]
  simp only [eq_ratCast]
  push_cast
  field_simp
  ring

end Zeta5Irr
