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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The uniform probability measure on a circle

For `c : ℂ` and `ε > 0`, the measure `ϖ_{c,ε}` is normalised arclength on the circle
`{z : |z - c| = ε}`: the image of the uniform probability measure on `(0, 2π]` under
`θ ↦ c + ε e^{iθ}`.

## Main definitions

* `Zeta5Irr.circleUnif c ε`: the measure `ϖ_{c,ε}`.

## Main results

* `Zeta5Irr.circleUnif.instIsProbabilityMeasure`: `ϖ_{c,ε}` is a probability measure.
* `Zeta5Irr.integral_circleUnif`: `∫ f dϖ_{c,ε} = (2π)⁻¹ ∫_0^{2π} f (c + ε e^{iθ}) dθ`.
* `Zeta5Irr.circleUnif_sphere_compl`: `ϖ_{c,ε}` is carried by the sphere `|z - c| = |ε|`.

## Implementation notes

* The source takes the uniform measure on `[0, 2π]`; we use `(0, 2π]`, which gives the same
  measure and matches the interval-integral convention, so that integrals against `ϖ_{c,ε}`
  become interval integrals in `θ`.
* The definition makes sense for every real `ε`; the hypothesis `ε > 0` is not needed for
  it to be a probability measure, and is left to the lemmas that use it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

open MeasureTheory Real Set Metric

namespace Zeta5Irr

/-- The uniform probability measure `ϖ_{c,ε}` on the circle `|z - c| = ε`: the pushforward of
the normalised Lebesgue measure on `(0, 2π]` under `θ ↦ c + ε e^{iθ}`. -/
@[zeta5irr "def_config_circle"]
noncomputable def circleUnif (c : ℂ) (ε : ℝ) : Measure ℂ :=
  Measure.map (circleMap c ε) ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc 0 (2 * π)))

/-- The normalised Lebesgue measure on `(0, 2π]` is a probability measure. -/
theorem isProbabilityMeasure_uniform_Ioc_zero_two_pi :
    IsProbabilityMeasure ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [pi_pos]) ENNReal.ofReal_ne_top

/-- `ϖ_{c,ε}` is a probability measure. -/
instance circleUnif.instIsProbabilityMeasure (c : ℂ) (ε : ℝ) :
    IsProbabilityMeasure (circleUnif c ε) :=
  haveI := isProbabilityMeasure_uniform_Ioc_zero_two_pi
  (Measure.isProbabilityMeasure_map_iff (measurable_circleMap c ε).aemeasurable).mpr this

/-- Integrals against `ϖ_{c,ε}` are averages over one turn of the circle:
`∫ f dϖ_{c,ε} = (2π)⁻¹ ∫_0^{2π} f (c + ε e^{iθ}) dθ`. -/
theorem integral_circleUnif {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (ε : ℝ) {f : ℂ → E} (hf : AEStronglyMeasurable f (circleUnif c ε)) :
    ∫ z, f z ∂circleUnif c ε = (2 * π)⁻¹ • ∫ θ in (0)..(2 * π), f (circleMap c ε θ) := by
  rw [circleUnif, integral_map (measurable_circleMap c ε).aemeasurable hf, integral_smul_measure,
    intervalIntegral.integral_of_le (by positivity), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]

/-- Integrals of continuous functions against `ϖ_{c,ε}` are averages over one turn of the
circle. -/
theorem integral_circleUnif_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (ε : ℝ) {f : ℂ → E} (hf : Continuous f) :
    ∫ z, f z ∂circleUnif c ε = (2 * π)⁻¹ • ∫ θ in (0)..(2 * π), f (circleMap c ε θ) :=
  integral_circleUnif c ε hf.aestronglyMeasurable

/-- `ϖ_{c,ε}` gives no mass to the complement of the sphere `|z - c| = |ε|`. -/
theorem circleUnif_sphere_compl (c : ℂ) (ε : ℝ) : circleUnif c ε (sphere c |ε|)ᶜ = 0 := by
  rw [circleUnif, Measure.map_apply (measurable_circleMap c ε)
    isClosed_sphere.isOpen_compl.measurableSet]
  convert measure_empty (μ := ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc (0 : ℝ) (2 * π))))
  ext θ
  simp

/-- `ϖ_{c,ε}`-almost every point lies on the sphere `|z - c| = |ε|`. -/
theorem ae_mem_sphere_circleUnif (c : ℂ) (ε : ℝ) : ∀ᵐ z ∂circleUnif c ε, z ∈ sphere c |ε| :=
  mem_ae_iff.mpr (circleUnif_sphere_compl c ε)

end Zeta5Irr
