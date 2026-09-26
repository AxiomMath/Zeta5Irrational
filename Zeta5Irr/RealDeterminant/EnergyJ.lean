/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.MeasureTheory.VectorMeasure.Integral
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
public import Mathlib.Topology.Sheaves.Init

/-!
# The Gaussian energy `J_ν(s)` of a signed measure

For a finite real signed Borel measure `ν` on `ℂ` and a real `s`, the Gaussian energy of `ν` is
the double integral
`J_ν(s) = ∬_{ℂ × ℂ} exp(-s |z - w|²) dν(z) dν(w)`.
It is a quadratic form in `ν`.

## Main definitions

* `Zeta5Irr.energyJ ν s`: the energy `J_ν(s)`.

## Main results

* `Zeta5Irr.energyJ_toSignedMeasure`: for a finite positive measure `μ`, `J_μ(s)` is the
  iterated Bochner integral `∫∫ exp(-s |z - w|²) dμ(z) dμ(w)`.
* `Zeta5Irr.energyJ_zero`: `J_0(s) = 0`.
* `Zeta5Irr.energyJ_neg`: `J_{-ν}(s) = J_ν(s)`.
* `Zeta5Irr.energyJ_smul`: `J_{cν}(s) = c² J_ν(s)`.

## Implementation notes

* The double integral is the iterated integral against `ν`, integrating first in `z` and then
  in `w`, using the integral of a real function against a real-valued vector measure,
  `∫ᵛ x, f x ∂<•ν`. For a positive finite measure this is the Bochner integral, and in
  general it agrees with the difference of the Bochner integrals against the two parts of the
  Jordan decomposition of `ν`. The kernel is bounded and continuous, so for a finite `ν` the
  iterated integral and the integral over `ℂ × ℂ` agree.
* The definition makes sense for every signed measure and every real `s`; compact support of
  `ν` and `s > 0` are hypotheses of the lemmas that use them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1: zero-mass logarithmic energy.
-/

@[expose] public section

open MeasureTheory VectorMeasure

namespace Zeta5Irr

/-- The Gaussian energy `J_ν(s) = ∬ exp(-s |z - w|²) dν(z) dν(w)` of a signed measure `ν`
on `ℂ`, as an iterated integral against `ν`. -/
@[zeta5irr "def_energy_J"]
noncomputable def energyJ (ν : SignedMeasure ℂ) (s : ℝ) : ℝ :=
  ∫ᵛ w, ∫ᵛ z, Real.exp (-s * ‖z - w‖ ^ 2) ∂<•ν ∂<•ν

/-- For a finite positive measure `μ`, the energy `J_μ(s)` is the iterated Bochner integral. -/
@[simp]
theorem energyJ_toSignedMeasure (μ : Measure ℂ) [IsFiniteMeasure μ] (s : ℝ) :
    energyJ μ.toSignedMeasure s = ∫ w, ∫ z, Real.exp (-s * ‖z - w‖ ^ 2) ∂μ ∂μ := by
  simp [energyJ]

/-- The energy of the zero measure vanishes. -/
@[simp]
theorem energyJ_zero (s : ℝ) : energyJ 0 s = 0 := by
  simp [energyJ, integral_zero_vectorMeasure]

/-- The energy is even in the measure: `J_{-ν}(s) = J_ν(s)`. -/
@[simp]
theorem energyJ_neg (ν : SignedMeasure ℂ) (s : ℝ) : energyJ (-ν) s = energyJ ν s := by
  simp only [energyJ, integral_neg_vectorMeasure, VectorMeasure.integral_fun_neg, neg_neg]

/-- The energy is quadratic in the measure: `J_{cν}(s) = c² J_ν(s)`. -/
theorem energyJ_smul (ν : SignedMeasure ℂ) (c s : ℝ) :
    energyJ (c • ν) s = c ^ 2 * energyJ ν s := by
  simp only [energyJ, integral_smul_vectorMeasure]
  rw [VectorMeasure.integral_fun_smul, smul_smul, sq, smul_eq_mul]

end Zeta5Irr
