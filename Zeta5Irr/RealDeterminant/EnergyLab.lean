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
# The zero-mass logarithmic energy `L_{a,b}(r)`

For `0 < a < b < ∞` and `r > 0`, the truncated logarithmic energy is
`L_{a,b}(r) = ½ ∫_a^b (e^{-s} - e^{-s r²}) / s ds`.
As `a → 0` and `b → ∞` this tends to `log r` (a Frullani integral), and it is the truncated
kernel used to represent `log r` in the real determinant estimates.

## Main definitions

* `Zeta5Irr.energyLab`: the function `L_{a,b}(r)`.

## Main results

* `Zeta5Irr.energyLab_self`: `L_{a,a}(r) = 0`.
* `Zeta5Irr.energyLab_symm`: `L_{b,a}(r) = -L_{a,b}(r)`.
* `Zeta5Irr.energyLab_one`: `L_{a,b}(1) = 0`.
* `Zeta5Irr.energyLab_neg`: `L_{a,b}(-r) = L_{a,b}(r)`.

## Implementation notes

* The function is total in all three real arguments: the integral is an interval integral
  `∫ s in a..b`, which is oriented and returns `0` on non-integrable integrands. The
  hypotheses `0 < a < b` and `r > 0` of the source are carried by the lemmas that need them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1: zero-mass logarithmic energy.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The zero-mass logarithmic energy
`L_{a,b}(r) = ½ ∫_a^b (e^{-s} - e^{-s r²}) / s ds`. In the source `0 < a < b` and `r > 0`;
here the definition is total, as an oriented interval integral. -/
@[zeta5irr "def_energy_Lab"]
noncomputable def energyLab (a b r : ℝ) : ℝ :=
  (1 / 2) * ∫ s in a..b, (exp (-s) - exp (-s * r ^ 2)) / s

/-- On a degenerate interval the energy vanishes. -/
@[simp]
theorem energyLab_self (a r : ℝ) : energyLab a a r = 0 := by
  simp [energyLab]

/-- Swapping the endpoints negates the energy. -/
theorem energyLab_symm (a b r : ℝ) : energyLab b a r = -energyLab a b r := by
  simp only [energyLab, intervalIntegral.integral_symm b a]
  ring

/-- At `r = 1` the integrand vanishes, so `L_{a,b}(1) = 0 = log 1`. -/
@[simp]
theorem energyLab_one (a b : ℝ) : energyLab a b 1 = 0 := by
  simp [energyLab]

/-- The energy depends on `r` only through `r²`. -/
@[simp]
theorem energyLab_neg (a b r : ℝ) : energyLab a b (-r) = energyLab a b r := by
  simp [energyLab]

end Zeta5Irr
