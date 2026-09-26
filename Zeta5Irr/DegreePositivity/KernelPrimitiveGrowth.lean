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
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
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

/-!
# The primitive grows slower than `e^{π y}`

For `b > 0` and `0 ≤ m ≤ 4`, the `m`-th derivative of `y ↦ y ^ 5 / (y ^ 2 + b ^ 2)` is
killed by the factor `e^{-π y}` as `y → ∞`:
`e^{-π y} (d/dy)^m (y ^ 5 / (y ^ 2 + b ^ 2)) → 0`.

The proof rests on the observation that differentiation preserves the shape
`p(y) / (y ^ 2 + b ^ 2) ^ n` with `p` a polynomial: by the quotient rule,
`(p / q ^ n)' = (p' q - n q' p) / q ^ (n + 1)` for `q = y ^ 2 + b ^ 2`. Hence the `m`-th
derivative of `y ^ 5 / (y ^ 2 + b ^ 2)` is `P(y) / (y ^ 2 + b ^ 2) ^ (m + 1)` for some
polynomial `P`. Since `(y ^ 2 + b ^ 2) ^ (m + 1) ≥ b ^ (2 (m + 1)) > 0`, it suffices that
`e^{-π y} P(y) → 0`, which is exponential decay dominating a polynomial.

## Main results

* `Zeta5Irr.exists_iteratedDeriv_eval_div_sq_add_sq_pow`: iterated derivatives of
  `p(y) / (y ^ 2 + b ^ 2) ^ n` have the form `P(y) / (y ^ 2 + b ^ 2) ^ (n + m)`.
* `Zeta5Irr.tendsto_exp_neg_mul_mul_eval`: `e^{-c y} p(y) → 0` for `c > 0`.
* `Zeta5Irr.tendsto_exp_neg_mul_iteratedDeriv_kernelPrimitive`: the growth estimate.

## Implementation notes

The source assumes `b > 0` and `0 ≤ m ≤ 4`, and argues via the division
`y ^ 5 / (y ^ 2 + b ^ 2) = y ^ 3 - b ^ 2 y + b ^ 4 y / (y ^ 2 + b ^ 2)`. The argument here
instead tracks the rational shape of all derivatives at once; it uses only `b ≠ 0` (so that
`y ^ 2 + b ^ 2` has no real zero) and works for every `m`, which is how the result is stated.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Filter Topology Polynomial Real

namespace Zeta5Irr

/-- For `b ≠ 0`, the `m`-th derivative of `p(y) / (y ^ 2 + b ^ 2) ^ n`, with `p` a
polynomial, is `P(y) / (y ^ 2 + b ^ 2) ^ (n + m)` for some polynomial `P`. -/
theorem exists_iteratedDeriv_eval_div_sq_add_sq_pow {b : ℝ} (hb : b ≠ 0) (p : ℝ[X]) (n m : ℕ) :
    ∃ P : ℝ[X], iteratedDeriv m (fun y => p.eval y / (y ^ 2 + b ^ 2) ^ n) =
      fun y => P.eval y / (y ^ 2 + b ^ 2) ^ (n + m) := by
  induction m with
  | zero => exact ⟨p, by simp⟩
  | succ m ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨derivative P * (X ^ 2 + C (b ^ 2)) - C ((n + m : ℕ) : ℝ) * (2 * X) * P, ?_⟩
    rw [iteratedDeriv_succ, hP]
    funext y
    have hq : y ^ 2 + b ^ 2 ≠ 0 := by positivity
    have h2 : HasDerivAt (fun y : ℝ => (y ^ 2 + b ^ 2) ^ (n + m))
        ((n + m : ℕ) * (y ^ 2 + b ^ 2) ^ (n + m - 1) * (2 * y)) y := by
      convert ((hasDerivAt_pow 2 y).add_const (b ^ 2)).pow (n + m) using 1
      simp
    have hd : HasDerivAt (fun y => P.eval y / (y ^ 2 + b ^ 2) ^ (n + m)) _ y :=
      (P.hasDerivAt y).div h2 (pow_ne_zero _ hq)
    rw [hd.deriv]
    simp only [eval_sub, eval_mul, eval_C, eval_add, eval_pow, eval_X, eval_ofNat]
    rw [← add_assoc]
    generalize n + m = k
    cases k with
    | zero => field_simp; simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      field_simp
      push_cast
      ring

/-- The polynomial shape of the iterated derivatives of `y ^ 5 / (y ^ 2 + b ^ 2)`. -/
theorem exists_iteratedDeriv_kernelPrimitive {b : ℝ} (hb : b ≠ 0) (m : ℕ) :
    ∃ P : ℝ[X], iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) =
      fun y => P.eval y / (y ^ 2 + b ^ 2) ^ (m + 1) := by
  obtain ⟨P, hP⟩ := exists_iteratedDeriv_eval_div_sq_add_sq_pow hb (X ^ 5) 1 m
  refine ⟨P, ?_⟩
  simpa [add_comm 1 m] using hP

/-- Exponential decay dominates a polynomial: `e^{-c y} p(y) → 0` as `y → ∞`, for `c > 0`. -/
theorem tendsto_exp_neg_mul_mul_eval {c : ℝ} (hc : 0 < c) (p : ℝ[X]) :
    Tendsto (fun y => rexp (-(c * y)) * p.eval y) atTop (𝓝 0) := by
  have h := (p.comp (C c⁻¹ * X)).tendsto_div_exp_atTop.comp
    (tendsto_id.const_mul_atTop hc)
  refine h.congr fun y => ?_
  simp [exp_neg, hc.ne', div_eq_inv_mul]

/-- **Growth of the primitive.** For `b ≠ 0` and every `m`,
`e^{-π y} (d/dy)^m (y ^ 5 / (y ^ 2 + b ^ 2)) → 0` as `y → ∞`. -/
@[zeta5irr "lem_w_ker_growth"]
theorem tendsto_exp_neg_mul_iteratedDeriv_kernelPrimitive {b : ℝ} (hb : b ≠ 0) (m : ℕ) :
    Tendsto (fun y => rexp (-(π * y)) *
      iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y) atTop (𝓝 0) := by
  obtain ⟨P, hP⟩ := exists_iteratedDeriv_kernelPrimitive hb m
  rw [hP]
  have hlim := ((tendsto_exp_neg_mul_mul_eval pi_pos P).abs.div_const ((b ^ 2) ^ (m + 1)))
  simp only [abs_zero, zero_div] at hlim
  refine squeeze_zero_norm (fun y => ?_) hlim
  have hb2 : 0 < b ^ 2 := by positivity
  have hle : (b ^ 2) ^ (m + 1) ≤ (y ^ 2 + b ^ 2) ^ (m + 1) :=
    pow_le_pow_left₀ hb2.le (by nlinarith [sq_nonneg y]) _
  rw [Real.norm_eq_abs, mul_div_assoc', abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 + b ^ 2) ^ (m + 1))]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hle

end Zeta5Irr
