/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SumIntegralComparisons
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# A uniform bound for the pole sums

For `y > 0` the function `t ↦ y / (y ^ 2 + t ^ 2)` is positive and decreasing on `[0, ∞)`,
with primitive `arctan (t / y)`. Comparing the sum with the integral gives, for every `V`,
`∑_{v = 1}^{V} y / (y ^ 2 + v ^ 2) ≤ ∫_0^V y / (y ^ 2 + t ^ 2) dt = arctan (V / y) < π / 2`,
a bound uniform in both `y` and `V`. In particular the series `∑_v y / (y ^ 2 + v ^ 2)`
converges.

## Main results

* `Zeta5Irr.sum_div_sq_add_sq_le_pi_div_two`: the bound `∑_{v=1}^{V} y / (y² + v²) ≤ π / 2`.
* `Zeta5Irr.sum_div_sq_add_sq_le`: the bound `∑_{v=1}^{V} y / (y² + v²) ≤ (1 + π) / 2`.
* `Zeta5Irr.sum_Icc_one_eq_sum_range`: `∑_{v=1}^{V} f v = ∑_{i<V} f (i + 1)`.
* `Zeta5Irr.summable_div_sq_add_sq`: the series `∑_{v ≥ 0} y / (y² + v²)` is summable.

## Implementation notes

The source bounds the term `v = 1` separately by `1 / 2` and compares only the terms
`v ≥ 2` with the integral over `[1, V]`, obtaining `(1 + π) / 2`. Comparing all terms
`v ≥ 1` with the integral over `[0, V]` gives the sharper constant `π / 2` directly, from
which the stated bound follows. The hypothesis `V ≥ 1` is dropped: the empty sum is `0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Real

namespace Zeta5Irr

/-- Reindex a sum over `Icc 1 V` as a sum over `range V`:
`∑_{v=1}^{V} f v = ∑_{i<V} f (i + 1)`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (V : ℕ) :
    ∑ v ∈ Finset.Icc 1 V, f v = ∑ i ∈ Finset.range V, f (i + 1) := by
  induction V with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- For `y > 0`, `∑_{v=1}^{V} y / (y ^ 2 + v ^ 2) ≤ π / 2`, by comparison with
`∫_0^V y / (y ^ 2 + t ^ 2) dt = arctan (V / y)`. -/
theorem sum_div_sq_add_sq_le_pi_div_two {y : ℝ} (hy : 0 < y) (V : ℕ) :
    ∑ v ∈ Finset.Icc 1 V, y / (y ^ 2 + (v : ℝ) ^ 2) ≤ π / 2 := by
  have hanti : AntitoneOn (fun t : ℝ => y / (y ^ 2 + t ^ 2)) (Set.Icc 0 (0 + (V : ℝ))) := by
    intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    apply div_le_div_of_nonneg_left hy.le (by positivity)
    nlinarith
  have h := hanti.sum_le_integral
  simp only [zero_add] at h
  have hint : ∫ t in (0 : ℝ)..V, y / (y ^ 2 + t ^ 2) = arctan (V / y) := by
    simp_rw [div_eq_mul_inv y]
    rw [intervalIntegral.integral_const_mul, integral_inv_sq_add_sq hy.ne']
    field_simp
    simp
  rw [hint] at h
  rw [sum_Icc_one_eq_sum_range]
  push_cast at h ⊢
  exact h.trans (arctan_lt_pi_div_two _).le

/-- **A uniform bound for the pole sums.** For `y > 0` and every `V`,
`∑_{v=1}^{V} y / (y ^ 2 + v ^ 2) ≤ (1 + π) / 2`. -/
@[zeta5irr "lem_w_sum_bound"]
theorem sum_div_sq_add_sq_le {y : ℝ} (hy : 0 < y) (V : ℕ) :
    ∑ v ∈ Finset.Icc 1 V, y / (y ^ 2 + (v : ℝ) ^ 2) ≤ (1 + π) / 2 :=
  (sum_div_sq_add_sq_le_pi_div_two hy V).trans (by linarith)

/-- For `y > 0` the series `∑_{v ≥ 0} y / (y ^ 2 + v ^ 2)` is summable. -/
theorem summable_div_sq_add_sq {y : ℝ} (hy : 0 < y) :
    Summable fun v : ℕ => y / (y ^ 2 + (v : ℝ) ^ 2) := by
  refine (summable_nat_add_iff 1).mp (summable_of_sum_range_le (c := π / 2)
    (fun n => by positivity) fun V => ?_)
  have := sum_div_sq_add_sq_le_pi_div_two hy V
  rw [sum_Icc_one_eq_sum_range] at this
  exact_mod_cast this

end Zeta5Irr
