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
# The logarithmic energy of a measure on `ℂ`

For a finite positive Borel measure `ρ` on `ℂ` with compact support, its logarithmic energy is
`I(ρ) = ∬_{ℂ × ℂ} log |t - u| dρ(t) dρ(u)`, whenever this integral is absolutely convergent.

## Main definitions

* `Zeta5Irr.logEnergy`: the logarithmic energy `I(ρ)`, as the Bochner integral of
  `(t, u) ↦ log ‖t - u‖` against the product measure `ρ ⊗ ρ`.

## Main results

* `Zeta5Irr.logEnergy_eq_integral_integral`: when the integrand is integrable for `ρ ⊗ ρ`,
  `I(ρ)` is the iterated integral `∫ t, ∫ u, log ‖t - u‖ ∂ρ ∂ρ`.
* `Zeta5Irr.logEnergy_zero`: the zero measure has energy `0`.
* `Zeta5Irr.logEnergy_smul`: `I(c • ρ) = c² I(ρ)` for `c : ℝ≥0∞` finite, `ρ` σ-finite.

## Implementation notes

* The definition is stated for an arbitrary measure `ρ` on `ℂ`; finiteness, compact support
  and absolute convergence are hypotheses of the lemmas that need them. The source leaves
  `I(ρ)` undefined when the integral is not absolutely convergent; here the Bochner integral
  is `0` by convention when its integrand is not integrable, a junk value that carries no
  meaning.
* On the diagonal `t = u` the integrand takes the value `Real.log 0 = 0`, whereas
  `log |t - u|` is not finite there. Whenever the source integral converges absolutely the
  diagonal is `ρ ⊗ ρ`-null, the integrand is integrable, and `logEnergy ρ` is exactly `I(ρ)`.
  The converse fails for measures with atoms: for a Dirac mass the diagonal has positive
  measure and the source integral does not converge absolutely, so `I(ρ)` is undefined, yet
  the Lean integrand is integrable (it vanishes `ρ ⊗ ρ`-almost everywhere) and `logEnergy` is
  `0`. Integrability in Lean therefore does not imply absolute convergence of the source
  integral, and statements about `I(ρ)` should carry the integrability of
  `(t, u) ↦ log ‖t - u‖` together with the nullity of the diagonal, or a hypothesis implying
  both.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

open scoped ENNReal

/-- The logarithmic energy `I(ρ) = ∬_{ℂ × ℂ} log |t - u| dρ(t) dρ(u)` of a measure `ρ` on `ℂ`,
as a Bochner integral against the product measure `ρ ⊗ ρ`. It is the energy of the source
whenever the integral converges absolutely, and `0` by convention otherwise. -/
@[zeta5irr "def_energy"]
noncomputable def logEnergy (ρ : Measure ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂ρ.prod ρ

/-- When `(t, u) ↦ log ‖t - u‖` is integrable for `ρ ⊗ ρ`, the logarithmic energy is the
iterated integral `∫ t, ∫ u, log ‖t - u‖ ∂ρ ∂ρ`. -/
theorem logEnergy_eq_integral_integral {ρ : Measure ℂ} [SFinite ρ]
    (h : Integrable (fun p : ℂ × ℂ ↦ Real.log ‖p.1 - p.2‖) (ρ.prod ρ)) :
    logEnergy ρ = ∫ t, ∫ u, Real.log ‖t - u‖ ∂ρ ∂ρ :=
  integral_prod _ h

/-- The zero measure has logarithmic energy `0`. -/
@[simp]
theorem logEnergy_zero : logEnergy 0 = 0 := by
  simp [logEnergy]

/-- The logarithmic energy is homogeneous of degree `2`: `I(c • ρ) = c² I(ρ)`. -/
theorem logEnergy_smul (ρ : Measure ℂ) [SFinite ρ] (c : ℝ≥0∞) :
    logEnergy (c • ρ) = c.toReal ^ 2 * logEnergy ρ := by
  simp only [logEnergy, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, smul_eq_mul, sq]

end Zeta5Irr
