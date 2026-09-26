/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.KernelSplit
public import Zeta5Irr.DegreePositivity.ProdIntegral

/-!
# A moment of the kernel `Ψ_b` against a simple pole

For `a, b > 0` this file evaluates
`∫_0^∞ y / (y² + a²) · Ψ_b(y) dy = π / (2 (a + b)⁵)`.

Write `p = y² + a²` and `q = y² + b²`. By the partial fractions of `Ψ_b`,
`y / p · Ψ_b(y) = y² / p · (q⁻³ - 12 b² q⁻⁴ + 16 b⁴ q⁻⁵)`, and `y² / p = 1 - a² / p`.
The integral is therefore a linear combination of the pure-power integrals
`Λ_m = ∫_0^∞ q^{-m}` and of the mixed integrals `Ξ_m = ∫_0^∞ p⁻¹ q^{-m}` for `m = 3, 4, 5`.
When `a = b` one has `Ξ_m = Λ_{m+1}`; when `a ≠ b` the mixed integrals are given by
partial fractions in `D = b² - a²`. In both cases the result is a rational identity.

## Main results

* `Zeta5Irr.integral_Ioi_div_sq_add_sq_mul_weightKernel`: the moment
  `∫_0^∞ y / (y² + a²) · Ψ_b(y) dy = π / (2 (a + b)⁵)`.

## Implementation notes

* The source first computes closed forms of `Θ_m = ∫_0^∞ y² / (p q^m)` for `m = 3, 4, 5`
  and then combines them. Here `Θ_m = Λ_m - a² Ξ_m` is expanded and the whole combination is
  verified as a single rational identity.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Set

namespace Zeta5Irr

/-- Pointwise decomposition of `y / (y² + a²) · Ψ_b(y)` into pure and mixed powers. -/
theorem div_sq_add_sq_mul_weightKernel {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (y : ℝ) :
    y / (y ^ 2 + a ^ 2) * weightKernel b y =
      ((y ^ 2 + b ^ 2) ^ 3)⁻¹ - 12 * b ^ 2 * ((y ^ 2 + b ^ 2) ^ 4)⁻¹
        + 16 * b ^ 4 * ((y ^ 2 + b ^ 2) ^ 5)⁻¹
        - a ^ 2 * (((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ 3)⁻¹
          - 12 * b ^ 2 * ((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ 4)⁻¹
          + 16 * b ^ 4 * ((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ 5)⁻¹) := by
  have hp : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hq : y ^ 2 + b ^ 2 ≠ 0 := by positivity
  rw [weightKernel_eq_split]
  field_simp
  ring

/-- **A moment of the kernel.** For `a, b > 0`,
`∫_0^∞ y / (y² + a²) · Ψ_b(y) dy = π / (2 (a + b)⁵)`. -/
@[zeta5irr "lem_w_ker_moment"]
theorem integral_Ioi_div_sq_add_sq_mul_weightKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ y in Ioi 0, y / (y ^ 2 + a ^ 2) * weightKernel b y = Real.pi / (2 * (a + b) ^ 5) := by
  have hL : ∀ m, 1 ≤ m → IntegrableOn (fun y : ℝ => ((y ^ 2 + b ^ 2) ^ m)⁻¹) (Ioi 0) :=
    fun m hm => (integrable_inv_sq_add_sq_pow hb.ne' hm).integrableOn
  have hX : ∀ m, IntegrableOn
      (fun y : ℝ => ((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ m)⁻¹) (Ioi 0) :=
    fun m => (integrable_inv_sq_add_sq_mul_sq_add_sq_pow ha.ne' hb.ne' m).integrableOn
  simp_rw [div_sq_add_sq_mul_weightKernel ha.ne' hb.ne']
  rw [integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_add, integral_sub, integral_const_mul, integral_const_mul]
  all_goals try
    repeat
      first
        | exact hL _ (by norm_num)
        | exact hX _
        | apply Integrable.sub
        | apply Integrable.add
        | refine Integrable.const_mul ?_ _
  · rw [integral_Ioi_inv_sq_add_sq_pow hb (m := 3) (by norm_num),
      integral_Ioi_inv_sq_add_sq_pow hb (m := 4) (by norm_num),
      integral_Ioi_inv_sq_add_sq_pow hb (m := 5) (by norm_num)]
    rcases eq_or_ne a b with rfl | hab
    · simp_rw [← pow_succ']
      rw [integral_Ioi_inv_sq_add_sq_pow hb (m := 4) (by norm_num),
        integral_Ioi_inv_sq_add_sq_pow hb (m := 5) (by norm_num),
        integral_Ioi_inv_sq_add_sq_pow hb (m := 6) (by norm_num)]
      norm_num [Nat.choose]
      field_simp
      ring
    · rw [integral_Ioi_inv_sq_add_sq_mul_sq_add_sq_pow ha hb hab,
        integral_Ioi_inv_sq_add_sq_mul_sq_add_sq_pow ha hb hab,
        integral_Ioi_inv_sq_add_sq_mul_sq_add_sq_pow ha hb hab]
      have hD : b ^ 2 - a ^ 2 ≠ 0 := by
        intro h
        apply hab
        nlinarith
      have hab' : a + b ≠ 0 := by positivity
      norm_num [Finset.sum_Icc_succ_top, Nat.choose]
      field_simp
      ring

end Zeta5Irr
