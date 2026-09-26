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
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.NumberTheory.ZetaValues
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The cubic kernel `G₀`

The cubic kernel is the real polynomial function
`G₀(v) = v (1 - v) (2v - 1) / 6`. It is the periodic antiderivative used to integrate the
quadratic `v (1 - v)` against the fractional part once more: its derivative is
`v (1 - v) - 1/6`, it vanishes at `0` and `1`, and it is odd about `1/2`. It equals
`-B₃(v) / 3`, where `B₃` is the third Bernoulli polynomial.

## Main definitions

* `Zeta5Irr.cubicKernel`: the function `v ↦ v (1 - v) (2v - 1) / 6` on `ℝ`.

## Main results

* `Zeta5Irr.cubicKernel_eq`: the expanded form `(-2v³ + 3v² - v) / 6`.
* `Zeta5Irr.cubicKernel_zero`, `Zeta5Irr.cubicKernel_one`: `G₀(0) = G₀(1) = 0`.
* `Zeta5Irr.cubicKernel_one_sub`: `G₀(1 - v) = -G₀(v)`.
* `Zeta5Irr.hasDerivAt_cubicKernel`: `G₀'(v) = v (1 - v) - 1/6`.
* `Zeta5Irr.continuous_cubicKernel`: `G₀` is continuous.
* `Zeta5Irr.cubicKernel_eq_neg_bernoulliFun`: `G₀(v) = -B₃(v) / 3`.

## Implementation notes

* The kernel is defined by the literal product rather than through `bernoulliFun 3`, so that
  evaluations, derivatives and bounds reduce by `ring`/`norm_num`; the identification with the
  Bernoulli function is recorded as a lemma.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9: the tail integral.
-/

@[expose] public section

namespace Zeta5Irr

/-- The cubic kernel `G₀(v) = v (1 - v) (2v - 1) / 6`. -/
@[zeta5irr "def_norm_G0"]
noncomputable def cubicKernel (v : ℝ) : ℝ := v * (1 - v) * (2 * v - 1) / 6

/-- The expanded form of the cubic kernel: `G₀(v) = (-2v³ + 3v² - v) / 6`. -/
theorem cubicKernel_eq (v : ℝ) : cubicKernel v = (-2 * v ^ 3 + 3 * v ^ 2 - v) / 6 := by
  unfold cubicKernel; ring

/-- `G₀(0) = 0`. -/
@[simp]
theorem cubicKernel_zero : cubicKernel 0 = 0 := by simp [cubicKernel]

/-- `G₀(1) = 0`. -/
@[simp]
theorem cubicKernel_one : cubicKernel 1 = 0 := by simp [cubicKernel]

/-- The cubic kernel is odd about `1/2`: `G₀(1 - v) = -G₀(v)`. -/
theorem cubicKernel_one_sub (v : ℝ) : cubicKernel (1 - v) = -cubicKernel v := by
  unfold cubicKernel; ring

/-- The derivative of the cubic kernel: `G₀'(v) = v (1 - v) - 1/6`. -/
theorem hasDerivAt_cubicKernel (v : ℝ) :
    HasDerivAt cubicKernel (v * (1 - v) - 1 / 6) v := by
  have h : HasDerivAt (fun v : ℝ => (-2 * v ^ 3 + 3 * v ^ 2 - v) / 6)
      ((-2 * (3 * v ^ 2) + 3 * (2 * v) - 1) / 6) v := by
    have := ((((hasDerivAt_pow 3 v).const_mul (-2)).add
      ((hasDerivAt_pow 2 v).const_mul 3)).sub (hasDerivAt_id v)).div_const 6
    convert this using 2 <;> simp
  convert h using 1
  · exact funext cubicKernel_eq
  · ring

/-- The derivative of the cubic kernel, as a `deriv` identity. -/
theorem deriv_cubicKernel (v : ℝ) : deriv cubicKernel v = v * (1 - v) - 1 / 6 :=
  (hasDerivAt_cubicKernel v).deriv

/-- The cubic kernel is differentiable. -/
theorem differentiable_cubicKernel : Differentiable ℝ cubicKernel :=
  fun v => (hasDerivAt_cubicKernel v).differentiableAt

/-- The cubic kernel is continuous. -/
@[fun_prop, continuity]
theorem continuous_cubicKernel : Continuous cubicKernel :=
  differentiable_cubicKernel.continuous

/-- The cubic kernel is `-1/3` times the third Bernoulli function: `G₀(v) = -B₃(v) / 3`. -/
theorem cubicKernel_eq_neg_bernoulliFun (v : ℝ) : cubicKernel v = -bernoulliFun 3 v / 3 := by
  simp [cubicKernel, bernoulliFun, Polynomial.bernoulli, Finset.sum_range_succ,
    bernoulli, bernoulli'_three, bernoulli'_two, bernoulli'_one, Nat.choose]
  ring

end Zeta5Irr
