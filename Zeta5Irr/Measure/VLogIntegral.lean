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
# The integral of `log (t + u²)`

For `t > 0` and every real `c`,
`∫₀^c log (t + u²) du = c log (t + c²) - 2c + 2 √t arctan (c / √t)`.
The right-hand side `F(c)` is an antiderivative of `u ↦ log (t + u²)` on all of `ℝ`
with `F(0) = 0`, so the identity is the fundamental theorem of calculus.

## Main results

* `Zeta5Irr.hasDerivAt_log_add_sq_antideriv`: `F' (u) = log (t + u²)`.
* `Zeta5Irr.integral_log_add_sq`: the closed form of `∫₀^c log (t + u²) du`.

## Implementation notes

* The source states the identity for `c > 0`; it holds for every real `c` (for `c < 0` both
  sides are odd in `c`), and it is stated here without that hypothesis.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For `t > 0`, `u ↦ u log (t + u²) - 2u + 2 √t arctan (u / √t)` has derivative
`log (t + u²)` at every real `u`. -/
theorem hasDerivAt_log_add_sq_antideriv {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun u => u * log (t + u ^ 2) - 2 * u + 2 * √t * arctan (u / √t))
      (log (t + u ^ 2)) u := by
  have hs : 0 < √t := sqrt_pos.2 ht
  have hpos : 0 < t + u ^ 2 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => t + u ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).const_add t
  have h3 := (hasDerivAt_id' u).mul (h1.log hpos.ne')
  have h4 := ((hasDerivAt_id' u).div_const √t).arctan
  have h5 := (h3.sub ((hasDerivAt_id' u).const_mul 2)).add (h4.const_mul (2 * √t))
  convert h5 using 1
  have hst : √t ^ 2 = t := sq_sqrt ht.le
  have := hpos.ne'
  field_simp
  rw [hst]
  ring

/-- For `t > 0` and every real `c`,
`∫₀^c log (t + u²) du = c log (t + c²) - 2c + 2 √t arctan (c / √t)`. -/
@[zeta5irr "lem_V_log_integral"]
theorem integral_log_add_sq {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, log (t + u ^ 2) =
      c * log (t + c ^ 2) - 2 * c + 2 * √t * arctan (c / √t) := by
  have hpos : ∀ u : ℝ, 0 < t + u ^ 2 := fun u => by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_log_add_sq_antideriv ht u)]
  · simp
  · exact ((continuous_const.add (continuous_pow 2)).log fun u => (hpos u).ne')
      |>.intervalIntegrable _ _

end Zeta5Irr
