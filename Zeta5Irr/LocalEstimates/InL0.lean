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
# The reserved zero-class dimension `L₀`

For an integer `M ≥ 40`, the inner range of the construction reserves `L₀ = 4 M + 10`
dimensions for the zero residue class. Together with the class dimensions `L_a`,
`1 ≤ a ≤ m°`, these add up to `h`.

## Main definitions

* `Zeta5Irr.zeroClassDim`: the reserved zero-class dimension `L₀ = 4 M + 10`.

## Main results

* `Zeta5Irr.cast_zeroClassDim`: the value of `L₀` in any semiring.
* `Zeta5Irr.le_zeroClassDim`: `170 ≤ L₀` when `40 ≤ M`.

## Implementation notes

* `L₀` is a dimension: it is the exponent of `(t + 0²)` in the row polynomials and the length
  of the range of the index `i` in the zero class. It is therefore a natural number, and so is
  `M`. The hypothesis `M ≥ 40` is not needed to define `L₀`; it is carried by the lemmas which
  use it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The reserved zero-class dimension `L₀ = 4 M + 10`. -/
@[zeta5irr "def_in_L0"]
def zeroClassDim (M : ℕ) : ℕ :=
  4 * M + 10

/-- The value of the reserved zero-class dimension, cast to any semiring. -/
@[simp, norm_cast]
theorem cast_zeroClassDim {R : Type*} [Semiring R] (M : ℕ) :
    (zeroClassDim M : R) = 4 * M + 10 := by
  simp [zeroClassDim]

/-- If `40 ≤ M` then `170 ≤ L₀`. -/
theorem le_zeroClassDim {M : ℕ} (hM : 40 ≤ M) : 170 ≤ zeroClassDim M := by
  unfold zeroClassDim
  omega

/-- The reserved zero-class dimension is positive. -/
theorem zeroClassDim_pos (M : ℕ) : 0 < zeroClassDim M := by
  unfold zeroClassDim
  omega

end Zeta5Irr
