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
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# A Gaussian as the square of a Gaussian convolution

For `s > 0` and `z w : ℂ`, the Gaussian `exp (-s |z - w|²)` is a convolution of two Gaussians of
twice the width parameter:
`exp (-s |z - w|²) = (4 s / π) ∫_ℂ exp (-2 s |z - u|²) exp (-2 s |w - u|²) dA(u)`,
where `A` is planar Lebesgue measure.

With `μ = (z + w) / 2`, the parallelogram identity
`|z - u|² + |w - u|² = 2 |u - μ|² + |z - w|² / 2` factors the integrand as
`exp (-s |z - w|²) exp (-4 s |u - μ|²)`, and after translating by `μ` the remaining integral is
the planar Gaussian integral `∫_ℂ exp (-4 s |u|²) dA(u) = π / (4 s)`.

## Main results

* `Zeta5Irr.integral_rexp_mul_norm_sub_sq`: `∫_ℂ exp (c |z - u|²) dA(u) = π / (-c)` for `c < 0`.
* `Zeta5Irr.exp_neg_mul_norm_sub_sq_eq_integral`: the identity above.

## Implementation notes

* Planar Lebesgue measure is the `volume` on `ℂ`, and `|·|` is the norm `‖·‖` on `ℂ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1: zero-mass logarithmic energy.
-/

@[expose] public section

namespace Zeta5Irr

open Real MeasureTheory

/-- The planar Gaussian integral `∫ exp(c |z - u|²) dA(u) = π / (-c)` for `c < 0`. -/
theorem integral_rexp_mul_norm_sub_sq {c : ℝ} (hc : c < 0) (z : ℂ) :
    ∫ u : ℂ, rexp (c * ‖z - u‖ ^ 2) = π / (-c) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := -c) (by linarith)
  simp only [neg_neg, Complex.finrank_real_complex] at h
  simp_rw [norm_sub_rev z]
  rw [integral_sub_right_eq_self (fun u => rexp (c * ‖u‖ ^ 2)) z, h]
  norm_num

/-- For `s > 0` and `z w : ℂ`,
`exp (-s ‖z - w‖²) = (4 s / π) ∫ u, exp (-2 s ‖z - u‖²) exp (-2 s ‖w - u‖²)`,
the integral being against planar Lebesgue measure. -/
@[zeta5irr "lem_energy_gauss_square"]
theorem exp_neg_mul_norm_sub_sq_eq_integral {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    rexp (-s * ‖z - w‖ ^ 2) =
      4 * s / π * ∫ u : ℂ, rexp (-2 * s * ‖z - u‖ ^ 2) * rexp (-2 * s * ‖w - u‖ ^ 2) := by
  set μ : ℂ := (z + w) / 2
  have key : ∀ u : ℂ, rexp (-2 * s * ‖z - u‖ ^ 2) * rexp (-2 * s * ‖w - u‖ ^ 2) =
      rexp (-s * ‖z - w‖ ^ 2) * rexp (-(4 * s) * ‖u - μ‖ ^ 2) := by
    intro u
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [μ, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im]
    norm_num
    ring
  simp_rw [key, norm_sub_rev _ μ]
  rw [integral_const_mul, integral_rexp_mul_norm_sub_sq (by linarith)]
  field_simp

end Zeta5Irr
