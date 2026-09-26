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
# The kernel `Ψ_b`

For a real parameter `b` this file defines the rational function
`Ψ_b(y) = (y⁵ - 10 b² y³ + 5 b⁴ y) / (y² + b²)⁵`.
It is the kernel through which the weight of the construction is integrated against
the simple poles `1 / (y² + b²)`: up to the factor `24 b⁴` it is the fourth derivative
of `y⁵ / (y² + b²)`. The numerator is the real part of `(y + i b)⁵`, so that
`Ψ_b(y) = Re((y + i b)⁵) / |y + i b|¹⁰ = Re((y - i b)⁻⁵)`.

## Main definitions

* `Zeta5Irr.weightKernel`: the kernel `Ψ_b(y)`.

## Main results

* `Zeta5Irr.weightKernel_neg_right`: `Ψ_b` is odd in `y`.
* `Zeta5Irr.weightKernel_neg_left`, `Zeta5Irr.weightKernel_abs_left`: `Ψ_b(y)` is even in `b`.
* `Zeta5Irr.weightKernel_zero_right`: `Ψ_b(0) = 0`.
* `Zeta5Irr.continuous_weightKernel`: `Ψ_b` is continuous for `b ≠ 0`.

## Implementation notes

* The source defines `Ψ_b` for `b > 0` only. Here it is defined for every real `b`,
  with the positivity hypothesis carried by the lemmas that need it; at `b = 0` the
  denominator vanishes at `y = 0` and the division is Lean's total division.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- The kernel `Ψ_b(y) = (y⁵ - 10 b² y³ + 5 b⁴ y) / (y² + b²)⁵`. -/
@[zeta5irr "def_wker"]
noncomputable def weightKernel (b y : ℝ) : ℝ :=
  (y ^ 5 - 10 * b ^ 2 * y ^ 3 + 5 * b ^ 4 * y) / (y ^ 2 + b ^ 2) ^ 5

/-- Unfolding lemma for `weightKernel`. -/
theorem weightKernel_def (b y : ℝ) :
    weightKernel b y = (y ^ 5 - 10 * b ^ 2 * y ^ 3 + 5 * b ^ 4 * y) / (y ^ 2 + b ^ 2) ^ 5 :=
  rfl

/-- `Ψ_b` is odd in `y`. -/
@[simp]
theorem weightKernel_neg_right (b y : ℝ) : weightKernel b (-y) = -weightKernel b y := by
  simp only [weightKernel]
  rw [← neg_div]
  congr 1 <;> ring

/-- `Ψ_b(y)` depends on `b` only through `b²`. -/
@[simp]
theorem weightKernel_neg_left (b y : ℝ) : weightKernel (-b) y = weightKernel b y := by
  simp [weightKernel, Even.neg_pow (by decide : Even 4)]

/-- `Ψ_b(0) = 0`. -/
@[simp]
theorem weightKernel_zero_right (b : ℝ) : weightKernel b 0 = 0 := by
  simp [weightKernel]

/-- `Ψ_b(y)` depends on `b` only through `|b|`. -/
theorem weightKernel_abs_left (b y : ℝ) : weightKernel |b| y = weightKernel b y := by
  simp [weightKernel, Even.pow_abs (by decide : Even 4)]

/-- For `b ≠ 0` the kernel `Ψ_b` is continuous. -/
theorem continuous_weightKernel {b : ℝ} (hb : b ≠ 0) : Continuous (weightKernel b) := by
  unfold weightKernel
  refine Continuous.div (by fun_prop) (by fun_prop) fun y => ?_
  have : 0 < y ^ 2 + b ^ 2 := by positivity
  positivity

end Zeta5Irr
