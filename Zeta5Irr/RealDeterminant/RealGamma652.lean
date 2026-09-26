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
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
# The Gram integral `∫₀^∞ t^{-1/2} (1 + √t)^5 e^{-√t} dt = 652`

The substitution `t = u²` turns the integral into `2 ∫₀^∞ (1 + u)^5 e^{-u} du`. Expanding
`(1 + u)^5` by the binomial theorem and evaluating each moment `∫₀^∞ u^k e^{-u} du = k!` through
the Gamma function gives `2 ∑_{k=0}^5 C(5,k) k! = 2 · 326 = 652`.

## Main results

* `Zeta5Irr.one_add_pow_le_two_pow_mul_one_add_pow`: `(1 + t)^L ≤ 2^L (1 + t^L)` for `t ≥ 0`.
* `Zeta5Irr.integral_Ioi_pow_mul_exp_neg_mul`: `∫₀^∞ uⁿ e^{-cu} du = n! / c^{n+1}` for `c > 0`.
* `Zeta5Irr.integrableOn_pow_mul_exp_neg_mul`: `u ↦ uⁿ e^{-cu}` is integrable on `(0, ∞)`.
* `Zeta5Irr.integral_one_add_pow_five_mul_exp_neg_Ioi`: `∫₀^∞ (1 + u)^5 e^{-u} du = 326`.
* `Zeta5Irr.integral_rpow_neg_half_mul_one_add_sqrt_pow_five_mul_exp_neg_sqrt`:
  `∫₀^∞ t^{-1/2} (1 + √t)^5 e^{-√t} dt = 652`.

## Implementation notes

The integral over `(0, ∞)` is the Bochner integral on `Set.Ioi 0`, and `t^{-1/2}` is the real
power `t ^ (-(1/2) : ℝ)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3: the Gram integral and scaling.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

open scoped Nat

/-- `(1 + t)^L ≤ 2^L (1 + t^L)` for `t ≥ 0`. -/
theorem one_add_pow_le_two_pow_mul_one_add_pow (L : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ L ≤ 2 ^ L * (1 + t ^ L) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ L ≤ 2 ^ L := pow_le_pow_left₀ (by linarith) (by linarith) L
      _ ≤ _ := by nlinarith [pow_nonneg ht L, pow_pos (two_pos (α := ℝ)) L]
  · calc (1 + t) ^ L ≤ (2 * t) ^ L := pow_le_pow_left₀ (by linarith) (by linarith) L
      _ = 2 ^ L * t ^ L := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg ht L, pow_pos (two_pos (α := ℝ)) L]

/-- For `c > 0` and `n : ℕ`, `∫_0^∞ yⁿ e^{-cy} dy = n! / c^{n+1}`. -/
theorem integral_Ioi_pow_mul_exp_neg_mul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), y ^ n * rexp (-(c * y)) = n ! / c ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hc
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, ← Nat.cast_succ, Real.rpow_natCast,
    div_pow, one_pow, one_div_mul_eq_div] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp [Real.rpow_natCast]

/-- For `k : ℕ` and `b > 0`, the function `y ↦ yᵏ e^{-by}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul (k : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => y ^ k * rexp (-(b * y))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := k) (p := 1)
    (by have := k.cast_nonneg (α := ℝ); linarith) one_pos hb).congr_fun (fun y _ => ?_)
    measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one, neg_mul]

/-- `∫₀^∞ (1 + u)^5 e^{-u} du = ∑_{k=0}^5 C(5,k) k! = 326`. -/
theorem integral_one_add_pow_five_mul_exp_neg_Ioi :
    ∫ x in Ioi (0 : ℝ), (1 + x) ^ 5 * exp (-x) = 326 := by
  have h : ∀ x : ℝ, (1 + x) ^ 5 * exp (-x) =
      ∑ k ∈ Finset.range 6, (Nat.choose 5 k : ℝ) * (x ^ k * exp (-(1 * x))) := by
    intro x
    simp [Finset.sum_range_succ, Nat.choose]
    ring
  simp_rw [h]
  rw [integral_finsetSum _ fun k _ => (integrableOn_pow_mul_exp_neg_mul k one_pos).const_mul _]
  simp_rw [integral_const_mul, integral_Ioi_pow_mul_exp_neg_mul _ one_pos]
  simp [Finset.sum_range_succ, Nat.factorial, Nat.choose]
  norm_num

/-- The Gram integral `∫₀^∞ t^{-1/2} (1 + √t)^5 e^{-√t} dt = 652`. -/
@[zeta5irr "lem_real_gamma_652"]
theorem integral_rpow_neg_half_mul_one_add_sqrt_pow_five_mul_exp_neg_sqrt :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (1 + √t) ^ 5 * exp (-√t) = 652 := by
  rw [← integral_comp_rpow_Ioi _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  have : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
      ((x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (1 + √(x ^ (2 : ℝ))) ^ 5 * exp (-√(x ^ (2 : ℝ))))
      = ∫ x in Ioi (0 : ℝ), 2 * ((1 + x) ^ 5 * exp (-x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx : 0 < x := hx
    have h2 : x ^ (2 : ℝ) = x ^ 2 := by norm_cast
    rw [h2, Real.sqrt_sq hx.le, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
  rw [this, integral_const_mul, integral_one_add_pow_five_mul_exp_neg_Ioi]
  norm_num

end Zeta5Irr
