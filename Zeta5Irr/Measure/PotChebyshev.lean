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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The Joukowski–Chebyshev factorisation on the unit circle

For `μ ∈ ℂ \ {0}` and `θ ∈ ℝ`,
`|(μ + μ⁻¹)/2 - cos θ| = |e^{iθ} - μ| · |e^{iθ} - μ⁻¹| / 2`.

Writing `z = e^{iθ}`, one has `z + z⁻¹ = 2 cos θ`, hence
`(z - μ)(z - μ⁻¹) = -2z((μ + μ⁻¹)/2 - cos θ)`, and taking absolute values with `|z| = 1`
gives the identity. It is the pointwise input to the potential of the arcsine measure.

## Main results

* `Zeta5Irr.mul_sub_exp_mul_I_sub_inv`: the factorisation
  `(e^{iθ} - μ)(e^{iθ} - μ⁻¹) = -2 e^{iθ} ((μ + μ⁻¹)/2 - cos θ)`.
* `Zeta5Irr.norm_joukowski_sub_cos`: the identity of absolute values.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.2: the arcsine measure and its potential.
-/

@[expose] public section

namespace Zeta5Irr

open Complex

/-- For `μ ≠ 0` and real `θ`, `(e^{iθ} - μ)(e^{iθ} - μ⁻¹) = -2 e^{iθ} ((μ + μ⁻¹)/2 - cos θ)`. -/
theorem mul_sub_exp_mul_I_sub_inv {μ : ℂ} (hμ : μ ≠ 0) (θ : ℝ) :
    (exp (θ * I) - μ) * (exp (θ * I) - μ⁻¹) =
      -2 * exp (θ * I) * ((μ + μ⁻¹) / 2 - Real.cos θ) := by
  have hz : exp (θ * I) ≠ 0 := exp_ne_zero _
  rw [ofReal_cos, cos, show -(θ : ℂ) * I = -(θ * I) by ring, exp_neg]
  field_simp
  ring

/-- **Joukowski–Chebyshev identity.** For `μ ≠ 0` and real `θ`,
`|(μ + μ⁻¹)/2 - cos θ| = |e^{iθ} - μ| · |e^{iθ} - μ⁻¹| / 2`. -/
@[zeta5irr "lem_pot_chebyshev"]
theorem norm_joukowski_sub_cos {μ : ℂ} (hμ : μ ≠ 0) (θ : ℝ) :
    ‖(μ + μ⁻¹) / 2 - Real.cos θ‖ = ‖exp (θ * I) - μ‖ * ‖exp (θ * I) - μ⁻¹‖ / 2 := by
  rw [← norm_mul, mul_sub_exp_mul_I_sub_inv hμ, norm_mul, norm_mul, norm_exp_ofReal_mul_I]
  simp

end Zeta5Irr
