/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.EnergyJNonneg
public import Zeta5Irr.RealDeterminant.EnergyLabBound
public import Zeta5Irr.RealDeterminant.EnergyLabDouble
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Nonpositivity of the zero-mass logarithmic energy

Let `ν` be a finite real signed measure on `ℂ` with total mass `ν(ℂ) = 0` whose logarithmic
kernel is absolutely integrable: `∬ |log |z - w|| d|ν|(z) d|ν|(w) < ∞`, where `|ν|` is the total
variation of `ν` and `|log 0| = ∞`. Then the logarithmic energy is nonpositive,
`∬ log |z - w| dν(z) dν(w) ≤ 0`.

The truncated kernels `L_{a,b}(r) = ½ ∫_a^b (e^{-s} - e^{-s r²}) / s ds` tend to `log r` as
`a → 0` and `b → ∞` and are dominated by `|log r|`, so by dominated convergence the energy is the
limit of `∬ L_{a,b}(|z - w|) dν(z) dν(w) = -½ ∫_a^b J_ν(s) / s ds`, and `J_ν(s) ≥ 0`.

## Main results

* `Zeta5Irr.continuous_energyLab`: for `a, b > 0`, `r ↦ L_{a,b}(r)` is continuous.
* `Zeta5Irr.tendsto_energyLab`: `L_{a,b}(r) → log r` as `a → 0⁺` and `b → ∞`, for `r > 0`.
* `Zeta5Irr.integral_integral_log_norm_sub_nonpos_of_integrable`: the energy is nonpositive,
  assuming `log |z - w|` is `|ν| ⊗ |ν|`-integrable and the diagonal is `|ν| ⊗ |ν|`-null.
* `Zeta5Irr.integral_integral_log_norm_sub_nonpos`: the energy is nonpositive under the
  source's hypothesis.

## Implementation notes

* In Mathlib `Real.log 0 = 0`, whereas in the source `|log |z - w||` is `+∞` on the diagonal
  `z = w`. The source's hypothesis is therefore stated as the finiteness of the lower Lebesgue
  integral of the `ℝ≥0∞`-valued function equal to `∞` on the diagonal and to `|log |z - w||`
  off it. This is equivalent to the conjunction of integrability of `log |z - w|` for
  `|ν| ⊗ |ν|` and nullity of the diagonal, which is the form of the intermediate result.
  Without the nullity of the diagonal the statement would be false for Mathlib's `log`
  (take `ν = δ₀ - δ_ε` with `0 < ε < 1`).
* The double integrals against `ν` are iterated integrals, integrating first in `z` and then in
  `w`, as in `Zeta5Irr.energyJ`. The total variation `|ν|` is `ν.variation`.
* The source also assumes that `ν` has compact support; this is not needed.
* The truncations are `a_n = 1 / (n + 1)` and `b_n = n + 1` for `n ∈ ℕ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1 (Zero-mass logarithmic energy).
-/

@[expose] public section

open MeasureTheory VectorMeasure Real Set Filter Topology
open scoped ENNReal

namespace Zeta5Irr

/-- For `a, b > 0`, the truncated energy `r ↦ L_{a,b}(r)` is continuous. -/
theorem continuous_energyLab {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (energyLab a b) := by
  set c := min a b
  have hc : 0 < c := lt_min ha hb
  have h : energyLab a b = fun r => (1 / 2) * ∫ s in a..b,
      (exp (-max c s) - exp (-max c s * r ^ 2)) / max c s := by
    ext r
    rw [energyLab]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    have : c ≤ s := by
      rw [uIcc, mem_Icc] at hs
      exact le_trans (le_of_eq (by simp [c])) hs.1
    simp only [max_eq_right this]
  rw [h]
  refine continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ a b)
  have : ∀ s : ℝ, max c s ≠ 0 := fun s => (lt_max_of_lt_left hc).ne'
  exact Continuous.div (by fun_prop) (by fun_prop) fun p => this p.2

/-- For `r > 0`, `L_{a,b}(r) → log r` as the lower endpoint tends to `0` from above and the upper
endpoint tends to `∞`. -/
theorem tendsto_energyLab {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {a b : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (ha' : ∀ᶠ i in l, 0 ≤ a i) (hb : Tendsto b l atTop) {r : ℝ}
    (hr : 0 < r) : Tendsto (fun i => energyLab (a i) (b i) r) l (𝓝 (log r)) := by
  set f : ℝ → ℝ := fun s => (exp (-s) - exp (-s * r ^ 2)) / s
  have hfi : IntegrableOn f (Ioi 0) := by
    have := integrableOn_exp_neg_mul_sub_exp_neg_mul_div one_pos (pow_pos hr 2)
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [f]; ring_nf
  have hcov : AECover (volume.restrict (Ioi (0 : ℝ))) l fun i => Ioc (a i) (b i) :=
    (aecover_Ioi_of_Ioi ha).inter (aecover_Iic hb)
  have hlim := hcov.integral_tendsto_of_countably_generated hfi
  rw [← half_integral_exp_neg_sub_exp_neg_mul_sq_div hr]
  refine (hlim.const_mul (1 / 2)).congr' ?_
  filter_upwards [ha', ha.eventually (gt_mem_nhds one_pos), hb.eventually_ge_atTop 1]
    with i h0 h1 h2
  rw [energyLab, intervalIntegral.integral_of_le (by linarith), Measure.restrict_restrict
    measurableSet_Ioc,
    inter_eq_left.2 (show Ioc (a i) (b i) ⊆ Ioi 0 from fun s hs => h0.trans_lt hs.1)]

/-- **Zero-mass logarithmic energy**, integrable form: if `ν(ℂ) = 0`, `log |z - w|` is
integrable for `|ν| ⊗ |ν|` and the diagonal is `|ν| ⊗ |ν|`-null, then
`∬ log |z - w| dν(z) dν(w) ≤ 0`. -/
theorem integral_integral_log_norm_sub_nonpos_of_integrable (ν : SignedMeasure ℂ)
    (hν : ν univ = 0)
    (hint : Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) (ν.variation.prod ν.variation))
    (hdiag : ν.variation.prod ν.variation (diagonal ℂ) = 0) :
    ∫ᵛ w, ∫ᵛ z, log ‖z - w‖ ∂<•ν ∂<•ν ≤ 0 := by
  have : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance
  set V := ν.variation
  set a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  set b : ℕ → ℝ := fun n => (n : ℝ) + 1
  have ha : ∀ n, 0 < a n := fun n => by positivity
  have hb : ∀ n, 0 < b n := fun n => by positivity
  have hcont : ∀ n, Continuous fun p : ℂ × ℂ => energyLab (a n) (b n) ‖p.1 - p.2‖ :=
    fun n => (continuous_energyLab (ha n) (hb n)).comp (by fun_prop)
  have hsing : ∀ᵐ w ∂V, V {w} = 0 := by
    have h := (Measure.measure_prod_null measurableSet_diagonal).1 hdiag
    filter_upwards [h] with w hw
    have e : Prod.mk w ⁻¹' diagonal ℂ = {w} := by ext z; simp [eq_comm]
    simpa [e] using hw
  have hsec := hint.prod_left_ae
  have hlim : ∀ r : ℝ, 0 < r → Tendsto (fun n => energyLab (a n) (b n) r) atTop (𝓝 (log r)) :=
    fun r hr => tendsto_energyLab tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall fun n => (ha n).le)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) hr
  have hbound : ∀ n (w : ℂ), V {w} = 0 →
      ∀ᵐ z ∂V, ‖energyLab (a n) (b n) ‖z - w‖‖ ≤ ‖log ‖z - w‖‖ := by
    intro n w hw
    filter_upwards [(measure_eq_zero_iff_ae_notMem).1 hw] with z hz
    have : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    simpa only [Real.norm_eq_abs] using abs_energyLab_le (ha n).le (hb n).le this
  have hinner : ∀ᵐ w ∂V, Tendsto (fun n => ∫ᵛ z, energyLab (a n) (b n) ‖z - w‖ ∂<•ν) atTop
      (𝓝 (∫ᵛ z, log ‖z - w‖ ∂<•ν)) := by
    filter_upwards [hsing, hsec] with w hw1 hw2
    refine tendsto_integral_of_dominated_convergence (fun z => ‖log ‖z - w‖‖)
      (fun n => ((hcont n).comp (continuous_id.prodMk continuous_const :
        Continuous fun z : ℂ => (z, w))).aestronglyMeasurable) hw2.norm (fun n => hbound n w hw1) ?_
    filter_upwards [(measure_eq_zero_iff_ae_notMem).1 hw1] with z hz
    exact hlim _ (norm_pos_iff.2 (sub_ne_zero.2 hz))
  have hT : Tendsto (fun n => ∫ᵛ w, ∫ᵛ z, energyLab (a n) (b n) ‖z - w‖ ∂<•ν ∂<•ν) atTop
      (𝓝 (∫ᵛ w, ∫ᵛ z, log ‖z - w‖ ∂<•ν ∂<•ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun w => ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ *
        ∫ z, ‖log ‖z - w‖‖ ∂V) (fun n => ?_) (hint.integral_norm_prod_right.const_mul _)
      (fun n => ?_) hinner
    · exact (StronglyMeasurable.integral_vectorMeasure_prod_left
        (f := fun z w => energyLab (a n) (b n) ‖z - w‖)
        (hcont n).stronglyMeasurable).aestronglyMeasurable
    · filter_upwards [hsing, hsec] with w hw1 hw2
      refine norm_integral_le_integral_norm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hw2.norm
        (hbound n w hw1)
  refine le_of_tendsto' hT fun n => ?_
  rw [integral_integral_energyLab ν hν (ha n) (hb n)]
  have hab : a n ≤ b n := by
    simp only [a, b]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have : 0 ≤ ∫ s in a n..b n, energyJ ν s / s :=
    intervalIntegral.integral_nonneg hab fun s hs =>
      div_nonneg (energyJ_nonneg ν ((ha n).trans_le hs.1)) ((ha n).le.trans hs.1)
  linarith

/-- **Zero-mass logarithmic energy** (Fauzan, §10.1): if `ν(ℂ) = 0` and
`∬ |log |z - w|| d|ν|(z) d|ν|(w) < ∞` (with `|log 0| = ∞`), then
`∬ log |z - w| dν(z) dν(w) ≤ 0`. -/
@[zeta5irr "lem_zero_mass_energy"]
theorem integral_integral_log_norm_sub_nonpos (ν : SignedMeasure ℂ) (hν : ν univ = 0)
    (hlog : ∫⁻ p : ℂ × ℂ, (if p.1 = p.2 then ∞ else ‖log ‖p.1 - p.2‖‖ₑ)
      ∂(ν.variation.prod ν.variation) < ∞) :
    ∫ᵛ w, ∫ᵛ z, log ‖z - w‖ ∂<•ν ∂<•ν ≤ 0 := by
  refine integral_integral_log_norm_sub_nonpos_of_integrable ν hν
    ⟨(by fun_prop : Measurable fun p : ℂ × ℂ => log ‖p.1 - p.2‖).aestronglyMeasurable,
      (lintegral_mono fun p => ?_).trans_lt hlog⟩ ?_
  · split_ifs
    · exact le_top
    · exact le_rfl
  · by_contra h
    refine hlog.ne (eq_top_iff.2 ?_)
    calc ∞ = ∫⁻ p, (diagonal ℂ).indicator (fun _ => ∞) p ∂(ν.variation.prod ν.variation) := by
          rw [lintegral_indicator_const measurableSet_diagonal, ENNReal.top_mul h]
      _ ≤ _ := lintegral_mono fun p => by
          by_cases hp : p.1 = p.2
          · simp [hp, indicator, mem_diagonal_iff]
          · simp [hp, indicator, mem_diagonal_iff]

end Zeta5Irr
