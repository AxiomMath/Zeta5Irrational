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
# The energy margin `U`

The rational constant
$$U = -\frac{2733991}{2000000},$$
which bounds from above the combination `λ M₀ - I(ρ) + C_*` of the comparison measure's
energy and the norm constant. It is the value that the final rational margins of the argument
are measured against.

## Main definitions

* `Zeta5Irr.energyMargin`: the real number `U = -2733991/2000000`.

## Main results

* `Zeta5Irr.energyMargin_eq`: the defining value, for rewriting without unfolding.
* `Zeta5Irr.energyMargin_lt`: `U < -136699/100000`.

## Implementation notes

The constant is rational, but every quantity it is compared with (`I(ρ)`, `C_*`, `A_M`) is
real, so it is defined directly as a real number.

## References

* Aabir Fauzan, *ζ(5) is irrational*, Lemma 6.1, equation (6.4), and §7.5
  (the final rational margin).
-/

@[expose] public section

namespace Zeta5Irr

/-- The energy margin `U = -2733991/2000000`. -/
@[zeta5irr "def_U"]
noncomputable def energyMargin : ℝ := -2733991 / 2000000

/-- The defining value of the energy margin `U`. -/
theorem energyMargin_eq : energyMargin = -2733991 / 2000000 := rfl

/-- The energy margin satisfies `U < -136699/100000`. -/
theorem energyMargin_lt : energyMargin < -136699 / 100000 := by
  rw [energyMargin_eq]; norm_num

/-- The energy margin `U` is negative. -/
theorem energyMargin_neg : energyMargin < 0 :=
  energyMargin_lt.trans (by norm_num)

end Zeta5Irr
