/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# A layer-cake formula for `log⁺`

Let `μ` be a finite positive Borel measure on `ℝ`, `z ∈ ℂ` and `δ > 0`. Then
`∫ log⁺ (δ / |z - u|) dμ(u) = ∫₀^δ μ {u : |z - u| < r} / r dr`,
where `log⁺ (δ / 0)` is read as `+∞`. The proof writes
`log⁺ (δ / d) = ∫₀^δ 𝟙_{d < r} dr / r` for every `d ≥ 0` and exchanges the order of
integration by Tonelli's theorem.

## Main results

* `Zeta5Irr.lintegral_Ioo_indicator_inv`: `∫₀^δ 𝟙_{d < r} dr / r = log⁺ (δ / d)` for `d > 0`,
  and `= ∞` for `d = 0`.
* `Zeta5Irr.lintegral_posLog_eq_lintegral_measure_div`: the layer-cake formula.

## Implementation notes

* Both sides are lower Lebesgue integrals in `ℝ≥0∞`. The integrand on the left is `∞` at
  `u = z` and `log⁺ (δ / ‖z - u‖)` elsewhere; the integral on the right is over `(0, δ)`.
* Tonelli's theorem needs only that `μ` is s-finite, so the formula is stated for s-finite
  measures, which include the finite ones.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

/-- For `δ > 0` and `d ≥ 0`, `∫₀^δ 𝟙_{d < r} dr / r` equals `∞` when `d = 0` and
`log⁺ (δ / d)` otherwise. -/
theorem lintegral_Ioo_indicator_inv {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d) :
    ∫⁻ r in Ioo 0 δ, (if d < r then ENNReal.ofReal r⁻¹ else 0) =
      if d = 0 then ⊤ else ENNReal.ofReal (posLog (δ / d)) := by
  split_ifs with h0
  · subst h0
    rw [setLIntegral_congr_fun (g := fun r => ENNReal.ofReal r⁻¹) measurableSet_Ioo
      (fun r hr => by simp only [hr.1, ite_true])]
    by_contra hne
    have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo 0 δ) := by
      refine ⟨by fun_prop, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal]
      · exact lt_top_iff_ne_top.2 hne
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact inv_nonneg.2 hr.1.le
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le).2 hint
    rw [intervalIntegrable_inv_iff] at this
    rcases this with h | h
    · exact hδ.ne h
    · exact h left_mem_uIcc
  · have hdpos : 0 < d := hd.lt_of_ne' h0
    rcases lt_or_ge d δ with hdδ | hdδ
    · have : (fun r : ℝ => if d < r then ENNReal.ofReal r⁻¹ else 0) =
          (Ioi d).indicator (fun r => ENNReal.ofReal r⁻¹) := by
        ext r
        simp [indicator]
      rw [this, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        inter_comm, Ioo_inter_Ioi, max_eq_right hdpos.le]
      have hint : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo d δ) := by
        have : IntervalIntegrable (fun r : ℝ => r⁻¹) volume d δ := by
          rw [intervalIntegrable_inv_iff]
          right
          rw [uIcc_of_le hdδ.le]
          exact fun h => lt_irrefl 0 (hdpos.trans_le h.1)
        rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hdδ.le] at this
      rw [← ofReal_integral_eq_lintegral_ofReal hint]
      · rw [← intervalIntegral.integral_of_le hdδ.le |>.trans
          (integral_Ioc_eq_integral_Ioo), integral_inv_of_pos hdpos hδ, posLog, max_eq_right]
        exact log_nonneg ((one_le_div hdpos).2 hdδ.le)
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact inv_nonneg.2 (hdpos.trans hr.1).le
    · rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Ioo
        (fun r hr => by simp only [not_lt.2 (hr.2.le.trans hdδ), ite_false]),
      lintegral_zero, posLog, max_eq_left]
      · simp
      · exact log_nonpos (div_nonneg hδ.le hd) ((div_le_one hdpos).2 hdδ)

/-- **Layer-cake formula for `log⁺`.** For an s-finite (in particular, a finite) measure `μ`
on `ℝ`, `z ∈ ℂ` and `δ > 0`,
`∫ log⁺ (δ / |z - u|) dμ(u) = ∫₀^δ μ {u : |z - u| < r} / r dr`, where `log⁺ (δ / 0) = ∞`. -/
@[zeta5irr "lem_config_layer_cake"]
theorem lintegral_posLog_eq_lintegral_measure_div (μ : Measure ℝ) [SFinite μ] (z : ℂ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∫⁻ u, (if z = u then ⊤ else ENNReal.ofReal (posLog (δ / ‖z - u‖))) ∂μ =
      ∫⁻ r in Ioo 0 δ, μ {u | ‖z - u‖ < r} / ENNReal.ofReal r := by
  calc ∫⁻ u, (if z = u then ⊤ else ENNReal.ofReal (posLog (δ / ‖z - u‖))) ∂μ
      = ∫⁻ u : ℝ, (∫⁻ r in Ioo 0 δ, if ‖z - u‖ < r then ENNReal.ofReal r⁻¹ else 0) ∂μ := by
        refine lintegral_congr fun u => ?_
        rw [lintegral_Ioo_indicator_inv hδ (norm_nonneg _)]
        simp only [norm_eq_zero, sub_eq_zero]
    _ = ∫⁻ r in Ioo 0 δ, ∫⁻ u : ℝ, (if ‖z - u‖ < r then ENNReal.ofReal r⁻¹ else 0) ∂μ :=
        lintegral_lintegral_swap (Measurable.ite (measurableSet_lt (by fun_prop)
          measurable_snd) (by fun_prop) measurable_const).aemeasurable
    _ = ∫⁻ r in Ioo 0 δ, μ {u | ‖z - u‖ < r} / ENNReal.ofReal r := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
        have hS : MeasurableSet {u : ℝ | ‖z - u‖ < r} :=
          measurableSet_lt (by fun_prop) measurable_const
        have : (fun u : ℝ => if ‖z - u‖ < r then ENNReal.ofReal r⁻¹ else 0) =
            {u : ℝ | ‖z - u‖ < r}.indicator fun _ => ENNReal.ofReal r⁻¹ := by
          ext u
          simp [indicator]
        rw [this, lintegral_indicator_const hS, ENNReal.ofReal_inv_of_pos hr.1, div_eq_mul_inv,
          mul_comm]

end Zeta5Irr
