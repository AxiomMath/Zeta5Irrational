/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.RingTheory.Radical.NatInt
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
# The arcsine measure

For reals `a < b`, the arcsine measure `ω_{[a,b]}` is the Borel measure on `ℝ` with density
`u ↦ 1 / (π √((u - a)(b - u)))` on the open interval `(a, b)` and `0` elsewhere, with respect
to Lebesgue measure. It is the equilibrium measure of the interval `[a, b]`, and it is the
image of the beta distribution `Beta(1/2, 1/2)` under the affine map `x ↦ a + (b - a) x`.

## Main definitions

* `Zeta5Irr.arcsinePDFReal`: the density of `ω_{[a,b]}`, as a real-valued function.
* `Zeta5Irr.arcsinePDF`: the density of `ω_{[a,b]}`, as an `ℝ≥0∞`-valued function.
* `Zeta5Irr.arcsineMeasure`: the arcsine measure `ω_{[a,b]}`.

## Main results

* `Zeta5Irr.ofReal_mul_arcsinePDF_affine`: the arcsine density on `[a, b]` pulled back along
  `x ↦ a + (b - a) x` and multiplied by the Jacobian `b - a` is the `Beta(1/2, 1/2)` density.
* `Zeta5Irr.lintegral_arcsinePDF_eq_one`: the arcsine density integrates to `1`.
* `Zeta5Irr.isProbabilityMeasure_arcsineMeasure`: `ω_{[a,b]}` is a probability measure.

## Implementation notes

* The endpoints `a` and `b` are arbitrary reals in the definitions; the hypothesis `a < b`
  appears only in the lemmas that need it. For `b ≤ a` the density vanishes identically and
  `ω_{[a,b]}` is the zero measure.
* Following `ProbabilityTheory.betaPDFReal` and `ProbabilityTheory.betaPDF`, the density is
  defined first as a real function and then as its `ENNReal.ofReal`, and the measure is
  `volume.withDensity` of the latter.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.2: the arcsine measure and its potential.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

/-- The density of the arcsine measure `ω_{[a,b]}`: `1 / (π √((u - a)(b - u)))` for
`a < u < b`, and `0` otherwise. -/
noncomputable def arcsinePDFReal (a b u : ℝ) : ℝ :=
  if u ∈ Ioo a b then (π * √((u - a) * (b - u)))⁻¹ else 0

/-- The density of the arcsine measure `ω_{[a,b]}`, as a function valued in `ℝ≥0∞`. -/
noncomputable def arcsinePDF (a b u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (arcsinePDFReal a b u)

/-- The arcsine measure `ω_{[a,b]}`: the measure on `ℝ` with density `arcsinePDF a b` with
respect to Lebesgue measure. -/
@[zeta5irr "def_arcsine"]
noncomputable def arcsineMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (arcsinePDF a b)

/-- Inside `(a, b)` the arcsine density is `1 / (π √((u - a)(b - u)))`. -/
lemma arcsinePDFReal_of_mem {a b u : ℝ} (hu : u ∈ Ioo a b) :
    arcsinePDFReal a b u = (π * √((u - a) * (b - u)))⁻¹ :=
  ite_eq_left hu

/-- Outside `(a, b)` the arcsine density vanishes. -/
lemma arcsinePDFReal_of_notMem {a b u : ℝ} (hu : u ∉ Ioo a b) :
    arcsinePDFReal a b u = 0 :=
  ite_eq_right hu

/-- Outside `(a, b)` the `ℝ≥0∞`-valued arcsine density vanishes. -/
lemma arcsinePDF_of_notMem {a b u : ℝ} (hu : u ∉ Ioo a b) : arcsinePDF a b u = 0 := by
  simp [arcsinePDF, arcsinePDFReal_of_notMem hu]

/-- The arcsine density is positive inside the interval. -/
lemma arcsinePDFReal_pos {a b u : ℝ} (hu : u ∈ Ioo a b) : 0 < arcsinePDFReal a b u := by
  rw [arcsinePDFReal_of_mem hu]
  have : 0 < (u - a) * (b - u) := mul_pos (sub_pos.2 hu.1) (sub_pos.2 hu.2)
  positivity

/-- The arcsine density is nonnegative. -/
lemma arcsinePDFReal_nonneg (a b u : ℝ) : 0 ≤ arcsinePDFReal a b u := by
  by_cases hu : u ∈ Ioo a b
  · exact (arcsinePDFReal_pos hu).le
  · rw [arcsinePDFReal_of_notMem hu]

/-- The arcsine density is measurable. -/
@[fun_prop]
lemma measurable_arcsinePDFReal (a b : ℝ) : Measurable (arcsinePDFReal a b) :=
  Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const

/-- The `ℝ≥0∞`-valued arcsine density is measurable. -/
@[fun_prop]
lemma measurable_arcsinePDF (a b : ℝ) : Measurable (arcsinePDF a b) :=
  (measurable_arcsinePDFReal a b).ennreal_ofReal

/-- `Beta(1/2, 1/2)` has normalising constant `π`. -/
lemma beta_one_half_one_half : beta (1 / 2) (1 / 2) = π := by
  rw [beta, Real.Gamma_one_half_eq, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.Gamma_one,
    div_one, Real.mul_self_sqrt pi_pos.le]

/-- The arcsine density on `[a, b]`, pulled back along `x ↦ a + (b - a) x` and multiplied by
the Jacobian `b - a`, is the density of `Beta(1/2, 1/2)`. -/
lemma ofReal_mul_arcsinePDF_affine {a b : ℝ} (hab : a < b) (x : ℝ) :
    ENNReal.ofReal (b - a) * arcsinePDF a b (a + (b - a) * x) = betaPDF (1 / 2) (1 / 2) x := by
  have hc : 0 < b - a := sub_pos.2 hab
  have hmem : a + (b - a) * x ∈ Ioo a b ↔ 0 < x ∧ x < 1 :=
    ⟨fun ⟨h₁, h₂⟩ ↦ ⟨pos_of_mul_pos_right (by linarith) hc.le, by nlinarith⟩,
      fun ⟨h₁, h₂⟩ ↦ ⟨by nlinarith, by nlinarith⟩⟩
  by_cases hx : 0 < x ∧ x < 1
  · rw [betaPDF_of_pos_lt_one hx.1 hx.2, arcsinePDF, arcsinePDFReal_of_mem (hmem.2 hx),
      ← ENNReal.ofReal_mul hc.le, beta_one_half_one_half]
    congr 1
    obtain ⟨h0, h1⟩ := hx
    have h1' : 0 < 1 - x := sub_pos.2 h1
    rw [show (a + (b - a) * x - a) * (b - (a + (b - a) * x)) = (b - a) ^ 2 * (x * (1 - x)) by
      ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le, Real.sqrt_mul h0.le,
      show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg h0.le, Real.rpow_neg h1'.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have := Real.sqrt_pos.2 h0
    have := Real.sqrt_pos.2 h1'
    field_simp
  · rw [betaPDF_eq, ite_eq_right hx, arcsinePDF_of_notMem (mt hmem.1 hx), mul_zero,
      ENNReal.ofReal_zero]

/-- The arcsine density on `[a, b]` integrates to `1`. -/
lemma lintegral_arcsinePDF_eq_one {a b : ℝ} (hab : a < b) : ∫⁻ u, arcsinePDF a b u = 1 := by
  have hc : 0 < b - a := sub_pos.2 hab
  have key : ∫⁻ x, arcsinePDF a b (a + (b - a) * x) =
      ENNReal.ofReal (b - a)⁻¹ * ∫⁻ u, arcsinePDF a b u := by
    have h := lintegral_map_equiv (μ := volume) (fun y ↦ arcsinePDF a b (a + y))
      (MeasurableEquiv.mulLeft₀ _ hc.ne')
    rw [MeasurableEquiv.coe_mulLeft₀, Real.map_volume_mul_left hc.ne', lintegral_smul_measure,
      abs_of_pos (inv_pos.2 hc), smul_eq_mul] at h
    rw [← lintegral_add_left_eq_self (arcsinePDF a b) a, ← h]
  have hβ := lintegral_betaPDF_eq_one (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)
  simp_rw [← ofReal_mul_arcsinePDF_affine hab] at hβ
  rwa [lintegral_const_mul _ (by fun_prop), key, ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
    mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul] at hβ

/-- For `a < b`, the arcsine measure `ω_{[a,b]}` is a probability measure. -/
lemma isProbabilityMeasure_arcsineMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (arcsineMeasure a b) where
  measure_univ := by simp [arcsineMeasure, lintegral_arcsinePDF_eq_one hab]

end Zeta5Irr
