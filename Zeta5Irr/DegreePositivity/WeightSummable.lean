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
# The defining series of the weight converges

For a real number `q` with `|q| < 1`, and in particular for `0 < q < 1`, the series
`∑_{ℓ ≥ 1} ℓ ^ 4 q ^ ℓ` is absolutely convergent. This is the series that defines the
weight of §2, so its convergence is what makes that definition meaningful.

## Main results

* `Zeta5Irr.summable_abs_natCast_pow_four_mul_pow`: `ℓ ↦ |ℓ ^ 4 q ^ ℓ|` is summable
  whenever `|q| < 1`.
* `Zeta5Irr.summable_natCast_pow_four_mul_pow`: the plain series is summable as well.

## Implementation notes

The series is indexed by `ℓ : ℕ`, so it includes the term at `ℓ = 0`; that term is
`0 ^ 4 q ^ 0 = 0`, so summability over `ℓ ≥ 0` is the same as summability over `ℓ ≥ 1`.
The source assumes `0 < q < 1`; the statement here assumes only `|q| < 1`, which that
hypothesis implies. The result is the case `k = 4` of
`summable_norm_pow_mul_geometric_of_norm_lt_one` over the reals.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- For real `q` with `|q| < 1`, the series `∑_{ℓ} ℓ ^ 4 q ^ ℓ` is absolutely convergent.
The index runs over `ℓ : ℕ`; the `ℓ = 0` term vanishes, so this is the series over `ℓ ≥ 1`. -/
@[zeta5irr "lem_w_summable"]
theorem summable_abs_natCast_pow_four_mul_pow {q : ℝ} (hq : |q| < 1) :
    Summable fun ℓ : ℕ => |(ℓ : ℝ) ^ 4 * q ^ ℓ| :=
  by simpa only [Real.norm_eq_abs] using
    summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 (r := q)
      (by rwa [Real.norm_eq_abs])

/-- For real `q` with `|q| < 1`, the series `∑_{ℓ} ℓ ^ 4 q ^ ℓ` converges. -/
theorem summable_natCast_pow_four_mul_pow {q : ℝ} (hq : |q| < 1) :
    Summable fun ℓ : ℕ => (ℓ : ℝ) ^ 4 * q ^ ℓ :=
  (summable_abs_natCast_pow_four_mul_pow hq).of_abs

end Zeta5Irr
