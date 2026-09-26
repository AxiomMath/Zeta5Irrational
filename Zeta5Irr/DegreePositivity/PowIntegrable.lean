/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
# Pure powers of `(y² + c²)⁻¹` are integrable

For a real `c ≠ 0` and a natural number `m ≥ 1`, the function `y ↦ (y² + c²)^{-m}` is integrable
on the whole real line, and hence on `(0, ∞)`.

## Main results

* `Zeta5Irr.integrable_inv_sq_add_sq_pow`: `y ↦ ((y² + c²)^m)⁻¹` is integrable on `ℝ`.
* `Zeta5Irr.integrableOn_inv_sq_add_sq_pow`: the same function is integrable on `(0, ∞)`.

## Implementation notes

The source states integrability on `(0, ∞)` for `c > 0`; we prove it on all of `ℝ` for
`c ≠ 0` and restrict. The proof dominates the function by a constant multiple of
`y ↦ (1 + (y / c)²)⁻¹`, which is integrable by rescaling `integrable_inv_one_add_sq`, in place
of the source's split of `(0, ∞)` at `1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory

namespace Zeta5Irr

/-- For `c ≠ 0` and `m ≥ 1`, the function `y ↦ ((y² + c²)^m)⁻¹` is integrable on `ℝ`. -/
theorem integrable_inv_sq_add_sq_pow {c : ℝ} (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun y : ℝ => ((y ^ 2 + c ^ 2) ^ m)⁻¹) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hc2 : 0 < c ^ 2 := by positivity
  refine ((integrable_inv_one_add_sq.comp_div hc).const_mul ((c ^ 2) ^ (k + 1))⁻¹).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  have hy : 0 < y ^ 2 + c ^ 2 := by positivity
  have h1 : 1 + (y / c) ^ 2 = (y ^ 2 + c ^ 2) / c ^ 2 := by field_simp; ring
  have h2 : (c ^ 2) ^ (k + 1) * ((y ^ 2 + c ^ 2) / c ^ 2) = (c ^ 2) ^ k * (y ^ 2 + c ^ 2) := by
    field_simp; ring
  rw [Real.norm_of_nonneg (by positivity), h1, ← mul_inv, h2, pow_succ]
  gcongr
  exact le_add_of_nonneg_left (sq_nonneg y)

/-- **Pure powers are integrable.** For `c ≠ 0` and `m ≥ 1`, the function
`y ↦ ((y² + c²)^m)⁻¹` is integrable on `(0, ∞)`. -/
@[zeta5irr "lem_w_pow_integrable"]
theorem integrableOn_inv_sq_add_sq_pow {c : ℝ} (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    IntegrableOn (fun y : ℝ => ((y ^ 2 + c ^ 2) ^ m)⁻¹) (Set.Ioi 0) :=
  (integrable_inv_sq_add_sq_pow hc hm).integrableOn

end Zeta5Irr
