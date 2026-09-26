/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.Parameters.Defs
public import Zeta5Irr.RealDeterminant.RealGamma652
public import Mathlib.NumberTheory.ZetaValues

/-!
# The even moments of the weight

For every natural number `e`, the `2e`-th moment of the weight is the Bernoulli moment:
`∫_0^∞ y^{2e} w(y) dy = m(e)`.

Expanding `w` as its defining series, `y^{2e} w(y) = (2π)⁴/12 · ∑_ℓ ℓ⁴ y^{2e+5} e^{-2πℓy}`.
Each term integrates to `(2π)⁴/12 · ℓ⁴ (2e+5)! / (2πℓ)^{2e+6}`, a Gamma integral, and the
sum of these is a multiple of `ζ(2e+2)`, which Euler's formula expresses through the
Bernoulli number `B_{2e+2}`.

## Main results

* `Zeta5Irr.integral_Ioi_pow_mul_weight`: `∫_0^∞ y^{2e} w(y) dy = m(e)`.

## Implementation notes

The source interchanges sum and integral by monotone convergence. Here the interchange is
`MeasureTheory.integral_tsum_of_summable_integral_norm`: every term is nonnegative on
`(0, ∞)`, so the summability of the integrals of the norms is the summability of the
integrals themselves, which is the convergence of `∑ ℓ^{-(2e+2)}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Real Set

open scoped Nat

namespace Zeta5Irr

/-- **The even moments of the weight.** For every `e : ℕ`,
`∫_0^∞ y^{2e} w(y) dy = m(e)`, the Bernoulli moment. -/
@[zeta5irr "lem_w_moment"]
theorem integral_Ioi_pow_mul_weight (e : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * weight y = (bernoulliMoment e : ℝ) := by
  set F : ℕ → ℝ → ℝ := fun ℓ y =>
    (2 * π) ^ 4 / 12 * (ℓ : ℝ) ^ 4 * (y ^ (2 * e + 5) * rexp (-(2 * π * ℓ * y))) with hF
  have hπ := pi_pos
  -- the integral of each term
  have hint : ∀ ℓ : ℕ, ∫ y in Ioi (0 : ℝ), F ℓ y =
      (2 * π) ^ 4 / 12 * ((2 * e + 5)! : ℝ) / (2 * π) ^ (2 * e + 5 + 1) *
        (1 / (ℓ : ℝ) ^ (2 * (e + 1))) := by
    intro ℓ
    rcases ℓ.eq_zero_or_pos with rfl | hℓ
    · simp [hF]
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    simp only [hF]
    rw [integral_const_mul, integral_Ioi_pow_mul_exp_neg_mul _ (by positivity)]
    field_simp
    ring
  -- each term is integrable
  have hFint : ∀ ℓ : ℕ, IntegrableOn (F ℓ) (Ioi 0) := by
    intro ℓ
    rcases ℓ.eq_zero_or_pos with rfl | hℓ
    · simp [hF]
    have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    exact (integrableOn_pow_mul_exp_neg_mul _ (by positivity)).const_mul _
  -- the integrals of the norms are the integrals
  have hnorm : ∀ ℓ : ℕ, ∫ y in Ioi (0 : ℝ), ‖F ℓ y‖ = ∫ y in Ioi (0 : ℝ), F ℓ y := by
    intro ℓ
    refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
    exact Real.norm_of_nonneg (by simp only [hF]; positivity)
  have hzeta := hasSum_zeta_nat (k := e + 1) (Nat.succ_ne_zero e)
  have hsum : HasSum (fun ℓ => ∫ y in Ioi (0 : ℝ), F ℓ y)
      ((2 * π) ^ 4 / 12 * ((2 * e + 5)! : ℝ) / (2 * π) ^ (2 * e + 5 + 1) *
        ((-1 : ℝ) ^ (e + 1 + 1) * (2 : ℝ) ^ (2 * (e + 1) - 1) * π ^ (2 * (e + 1)) *
          bernoulli (2 * (e + 1)) / (2 * (e + 1))!)) := by
    simpa only [hint] using hzeta.mul_left _
  -- the integrand is the sum of the series
  have hser : ∀ y ∈ Ioi (0 : ℝ), y ^ (2 * e) * weight y = ∑' ℓ : ℕ, F ℓ y := by
    intro y _
    rw [weight, ← mul_assoc, ← tsum_mul_left]
    congr 1 with ℓ
    simp only [hF]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hser,
    ← integral_tsum_of_summable_integral_norm hFint (by simpa only [hnorm] using hsum.summable),
    hsum.tsum_eq]
  rw [show 2 * (e + 1) - 1 = 2 * e + 1 by omega, show 2 * (e + 1) = 2 * e + 2 by ring,
    show 2 * e + 5 = (2 * e + 2) + 3 by ring, bernoulliMoment]
  simp only [Nat.factorial_succ, Nat.add_assoc]
  push_cast
  have : (0 : ℝ) < ((2 * e + 2)! : ℕ) := by exact_mod_cast Nat.factorial_pos _
  field_simp
  ring

end Zeta5Irr
