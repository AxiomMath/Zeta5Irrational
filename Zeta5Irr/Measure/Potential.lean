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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init

/-!
# The logarithmic potential of a measure on `ℂ`

For a finite positive Borel measure `ρ` on `ℂ` with compact support and `t ∈ ℂ`, the
logarithmic potential of `ρ` at `t` is `U^ρ(t) = ∫_ℂ log |t - u| dρ(u)`, whenever this integral
is absolutely convergent.

## Main definitions

* `Zeta5Irr.logPotential`: the logarithmic potential `U^ρ(t)`, as the Bochner integral of
  `u ↦ log ‖t - u‖` against `ρ`.

## Main results

* `Zeta5Irr.logPotential_zero`: the zero measure has potential `0`.
* `Zeta5Irr.logPotential_smul`: `U^{c • ρ} = c U^ρ` for `c : ℝ≥0∞`.
* `Zeta5Irr.logPotential_add`: `U^{ρ + σ}(t) = U^ρ(t) + U^σ(t)` under integrability.
* `Zeta5Irr.logPotential_dirac`: `U^{δ_a}(t) = log |t - a|`.
* `Zeta5Irr.logPotential_map_ofReal`: for a measure `μ` on `ℝ` and `t ∈ ℝ`,
  `U^{μ}(t) = ∫ log |t - u| dμ(u)`, the potential being that of the image of `μ` in `ℂ`.

## Implementation notes

* The definition is stated for an arbitrary measure `ρ` on `ℂ`; finiteness, compact support
  and absolute convergence are hypotheses of the lemmas that need them. The Bochner integral
  is `0` by convention when its integrand is not integrable, so `logPotential ρ t` is `U^ρ(t)`
  exactly when the source integral converges absolutely.
* At `u = t` the integrand takes the value `Real.log 0 = 0` rather than `-∞`. This only matters
  when `ρ` has an atom at `t`, where the source integral diverges.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

open scoped ENNReal

/-- The logarithmic potential `U^ρ(t) = ∫_ℂ log |t - u| dρ(u)` of a measure `ρ` on `ℂ` at a
point `t`, as a Bochner integral. It is the potential of the source whenever the integral
converges absolutely, and `0` by convention otherwise. -/
@[zeta5irr "def_potential"]
noncomputable def logPotential (ρ : Measure ℂ) (t : ℂ) : ℝ :=
  ∫ u, Real.log ‖t - u‖ ∂ρ

/-- The zero measure has logarithmic potential `0`. -/
@[simp]
theorem logPotential_zero : logPotential 0 = 0 := by
  ext t
  simp [logPotential]

/-- The logarithmic potential is homogeneous: `U^{c • ρ} = c U^ρ`. -/
theorem logPotential_smul (ρ : Measure ℂ) (c : ℝ≥0∞) (t : ℂ) :
    logPotential (c • ρ) t = c.toReal * logPotential ρ t := by
  simp [logPotential, integral_smul_measure]

/-- The logarithmic potential is additive in the measure, where both potentials converge
absolutely. -/
theorem logPotential_add {ρ σ : Measure ℂ} {t : ℂ}
    (hρ : Integrable (fun u ↦ Real.log ‖t - u‖) ρ)
    (hσ : Integrable (fun u ↦ Real.log ‖t - u‖) σ) :
    logPotential (ρ + σ) t = logPotential ρ t + logPotential σ t :=
  integral_add_measure hρ hσ

/-- The logarithmic potential of the Dirac mass at `a` is `t ↦ log |t - a|`. -/
@[simp]
theorem logPotential_dirac (a t : ℂ) : logPotential (Measure.dirac a) t = Real.log ‖t - a‖ := by
  simp [logPotential]

/-- The potential of the image in `ℂ` of a measure `μ` on `ℝ`, at a point `z ∈ ℂ`, is
`∫ log ‖z - u‖ dμ(u)`. -/
theorem logPotential_map_ofReal_eq_integral_norm (μ : Measure ℝ) (z : ℂ) :
    logPotential (μ.map ((↑) : ℝ → ℂ)) z = ∫ u, Real.log ‖z - u‖ ∂μ :=
  integral_map Complex.measurable_ofReal.aemeasurable
    (by fun_prop : Measurable fun w : ℂ ↦ Real.log ‖z - w‖).aestronglyMeasurable

/-- The potential of the image in `ℂ` of a measure `μ` on `ℝ`, at a real point `t`, is the real
integral `∫ log |t - u| dμ(u)`. -/
theorem logPotential_map_ofReal (μ : Measure ℝ) (t : ℝ) :
    logPotential (μ.map ((↑) : ℝ → ℂ)) t = ∫ u, Real.log |t - u| ∂μ := by
  simp_rw [logPotential_map_ofReal_eq_integral_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

end Zeta5Irr
