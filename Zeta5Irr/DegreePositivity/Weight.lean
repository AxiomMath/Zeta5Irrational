/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The weight

For `y > 0` the weight of the method is
`w(y) = (2π)⁴ y⁵ / 12 · ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}`.
It is the density on `(0, ∞)` against which the rational functional of the
construction is integrated: the Bernoulli moments are its even moments and the
harmonic sums of order five arise from integrating it against simple poles.

## Main definitions

* `Zeta5Irr.weight`: the weight `w`.

## Main results

* `Zeta5Irr.weight_eq_tsum_succ`: the series defining `w` may be indexed from
  `ℓ = 1`, as in the source.
* `Zeta5Irr.weight_zero`: `w(0) = 0`.

## Implementation notes

* The source defines `w(y)` only for `y > 0`. Here `weight` is a function on all
  of `ℝ`, defined by the same formula with the series taken as a `tsum`; only
  its values at `y > 0` carry meaning. For `y ≤ 0` the series diverges and the
  `tsum` is `0` by convention, so `weight y = 0` there.
* The series is indexed by `ℓ : ℕ` rather than `ℓ ≥ 1`: the term at `ℓ = 0`
  vanishes, so the two sums agree (`Zeta5Irr.weight_eq_tsum_succ`), and indexing
  by `ℕ` avoids a subtype or a shift in every downstream computation.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The weight `w(y) = (2π)⁴ y⁵ / 12 · ∑_{ℓ ≥ 1} ℓ⁴ e^{-2πℓy}`. It is meaningful for
`y > 0`; the `ℓ = 0` term of the series vanishes, and for `y ≤ 0` the series diverges, so
the value there is `0` by the `tsum` convention. -/
@[zeta5irr "def_w"]
noncomputable def weight (y : ℝ) : ℝ :=
  (2 * π) ^ 4 * y ^ 5 / 12 * ∑' ℓ : ℕ, (ℓ : ℝ) ^ 4 * rexp (-(2 * π * ℓ * y))

/-- The series defining the weight, indexed from `ℓ = 1` as in the source. -/
theorem weight_eq_tsum_succ (y : ℝ) :
    weight y = (2 * π) ^ 4 * y ^ 5 / 12 *
      ∑' ℓ : ℕ, ((ℓ + 1 : ℕ) : ℝ) ^ 4 * rexp (-(2 * π * (ℓ + 1 : ℕ) * y)) := by
  rw [weight]
  congr 1
  refine (Nat.succ_injective.tsum_eq fun n hn => ?_).symm
  rcases n with _ | n
  · simp at hn
  · exact ⟨n, rfl⟩

/-- The weight vanishes at `0`. -/
@[simp]
theorem weight_zero : weight 0 = 0 := by
  simp [weight]

end Zeta5Irr
