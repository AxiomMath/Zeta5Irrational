/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.PowIntegral

/-!
# The integral of `(y² + a²)⁻¹ (y² + b²)^{-m}` over `(0, ∞)`

For reals `a, b > 0` with `a ≠ b`, write `D = b² - a²` and
`Λ_k = π / (2 b^{2k-1}) · 4^{-(k-1)} · binom(2k-2, k-1) = ∫_0^∞ dy / (y² + b²)^k`. Then
`∫_0^∞ dy / ((y² + a²)(y² + b²)^m) = π / (2 a D^m) - ∑_{k=1}^m Λ_k / D^{m+1-k}`.

The proof is by induction on `m`, using the partial fraction identity
`1 / ((y² + a²)(y² + b²)^{m+1}) = D⁻¹ (1 / ((y² + a²)(y² + b²)^m) - 1 / (y² + b²)^{m+1})`.

## Main results

* `Zeta5Irr.integrable_inv_sq_add_sq_mul_sq_add_sq_pow`: the integrand is integrable on `ℝ`.
* `Zeta5Irr.inv_sq_add_sq_mul_sq_add_sq_pow_succ`: the partial fraction identity.
* `Zeta5Irr.integral_Ioi_inv_sq_add_sq_mul_sq_add_sq_pow`: the closed form.

## Implementation notes

The source states the closed form for `m ≥ 1`; it also holds for `m = 0`, where the sum is
empty and the formula reduces to `∫_0^∞ dy / (y² + a²) = π / (2a)`, so no lower bound on `m`
is assumed and the induction starts at `m = 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Set

namespace Zeta5Irr

/-- For `a ≠ 0` and `b ≠ 0`, `y ↦ ((y² + a²)(y² + b²)^m)⁻¹` is integrable on `ℝ`. -/
theorem integrable_inv_sq_add_sq_mul_sq_add_sq_pow {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℕ) :
    Integrable (fun y : ℝ => ((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ m)⁻¹) := by
  refine (((integrable_inv_sq_add_sq_pow ha le_rfl).const_mul ((b ^ 2) ^ m)⁻¹)).mono'
    (by fun_prop) (.of_forall fun y => ?_)
  have h1 : 0 < y ^ 2 + a ^ 2 := by positivity
  have hb2 : 0 < b ^ 2 := by positivity
  have h2 : (b ^ 2) ^ m ≤ (y ^ 2 + b ^ 2) ^ m := pow_le_pow_left₀ hb2.le (by nlinarith) m
  rw [Real.norm_eq_abs, pow_one, abs_of_pos (by positivity), mul_inv, mul_comm]
  gcongr

/-- **Partial fractions.** For `a, b ≠ 0`, with `D = b² - a² ≠ 0`,
`1 / ((y² + a²)(y² + b²)^{m+1}) = D⁻¹ (1 / ((y² + a²)(y² + b²)^m) - 1 / (y² + b²)^{m+1})`. -/
theorem inv_sq_add_sq_mul_sq_add_sq_pow_succ {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : b ^ 2 - a ^ 2 ≠ 0) (y : ℝ) (m : ℕ) :
    ((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ (m + 1))⁻¹ =
      (b ^ 2 - a ^ 2)⁻¹ *
        (((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ m)⁻¹ - ((y ^ 2 + b ^ 2) ^ (m + 1))⁻¹) := by
  have h1 : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h2 : y ^ 2 + b ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- For `a, b > 0` with `a ≠ b`, writing `D = b² - a²`,
`∫_0^∞ dy / ((y² + a²)(y² + b²)^m) = π / (2 a D^m) - ∑_{k=1}^m D^{-(m+1-k)} Λ_k`, where
`Λ_k = π / (2 b^{2k-1}) · 4^{-(k-1)} · binom(2k-2, k-1) = ∫_0^∞ dy / (y² + b²)^k`. -/
@[zeta5irr "lem_w_prod_int"]
theorem integral_Ioi_inv_sq_add_sq_mul_sq_add_sq_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (m : ℕ) :
    ∫ y in Ioi (0 : ℝ), ((y ^ 2 + a ^ 2) * (y ^ 2 + b ^ 2) ^ m)⁻¹ =
      Real.pi / (2 * a * (b ^ 2 - a ^ 2) ^ m) -
        ∑ k ∈ Finset.Icc 1 m, 1 / (b ^ 2 - a ^ 2) ^ (m + 1 - k) *
          (Real.pi / (2 * b ^ (2 * k - 1)) * (1 / 4 ^ (k - 1)) *
            ((2 * k - 2).choose (k - 1) : ℝ)) := by
  have hD : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    apply hab
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  induction m with
  | zero =>
    simp only [pow_zero, mul_one, Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty,
      sub_zero]
    exact integral_Ioi_inv_sq_add_sq ha
  | succ m ih =>
    simp_rw [inv_sq_add_sq_mul_sq_add_sq_pow_succ ha.ne' hb.ne' hD]
    rw [integral_const_mul, integral_sub
      (integrable_inv_sq_add_sq_mul_sq_add_sq_pow ha.ne' hb.ne' m).integrableOn
      (integrableOn_inv_sq_add_sq_pow hb.ne' (Nat.le_add_left 1 m)), ih,
      integral_Ioi_inv_sq_add_sq_pow hb (Nat.le_add_left 1 m),
      Finset.sum_Icc_succ_top (Nat.le_add_left 1 m), mul_sub, mul_sub, Finset.mul_sum]
    have hsum : ∀ k ∈ Finset.Icc 1 m, (b ^ 2 - a ^ 2)⁻¹ * (1 / (b ^ 2 - a ^ 2) ^ (m + 1 - k) *
        (Real.pi / (2 * b ^ (2 * k - 1)) * (1 / 4 ^ (k - 1)) *
          ((2 * k - 2).choose (k - 1) : ℝ))) =
        1 / (b ^ 2 - a ^ 2) ^ (m + 1 + 1 - k) *
          (Real.pi / (2 * b ^ (2 * k - 1)) * (1 / 4 ^ (k - 1)) *
            ((2 * k - 2).choose (k - 1) : ℝ)) := by
      intro k hk
      have hk : m + 1 + 1 - k = (m + 1 - k) + 1 := by
        have := (Finset.mem_Icc.1 hk).2
        omega
      rw [hk, pow_succ]
      field_simp
      ring
    rw [Finset.sum_congr rfl hsum, Nat.add_sub_cancel_left, pow_one, pow_succ]
    field_simp
    ring

end Zeta5Irr
