/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.EncSqrt

/-!
# Accuracy of the rational square-root enclosure

For a rational `x ≥ 0`, the enclosure `s(x) = 2^{-144} max {n ∈ ℤ_{≥0} : n² ≤ 2^{288} x}`
satisfies `s(x) ≤ √x ≤ s(x) + 2^{-144}`. If `n₀` is the maximum, then
`n₀² ≤ 2^{288} x < (n₀ + 1)²`; dividing by `2^{288}` and taking square roots gives the
enclosure.

## Main results

* `Zeta5Irr.sqrtApprox_le_sqrt`: `s(x) ≤ √x`.
* `Zeta5Irr.sqrt_le_sqrtApprox_add`: `√x ≤ s(x) + 2^{-144}`.

## Implementation notes

The lower bound `s(x) ≤ √x` holds for every rational `x`: for `x < 0` both sides vanish.
Only the upper bound uses `x ≥ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4 (Elementary enclosures).
-/

@[expose] public section

namespace Zeta5Irr

set_option exponentiation.threshold 300 in
/-- The square-root enclosure is a lower bound: `s(x) ≤ √x`. -/
@[zeta5irr "lem_enc_sqrt"]
theorem sqrtApprox_le_sqrt (x : ℚ) : (sqrtApprox x : ℝ) ≤ √(x : ℝ) := by
  rcases lt_or_ge x 0 with hx | hx
  · have h : ⌊(2 : ℚ) ^ 288 * x⌋₊ = 0 :=
      Nat.floor_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx.le)
    simp [sqrtApprox, sqrtApproxNum, h, Real.sqrt_nonneg]
  have h := (sq_le_iff_le_sqrtApproxNum hx (sqrtApproxNum x)).2 le_rfl
  have h' : ((sqrtApproxNum x : ℝ)) ^ 2 ≤ 2 ^ 288 * (x : ℝ) := by exact_mod_cast h
  rw [sqrtApprox]
  push_cast
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc (sqrtApproxNum x : ℝ) ^ 2 ≤ 2 ^ 288 * (x : ℝ) := h'
    _ = x * (2 ^ 144) ^ 2 := by rw [← pow_mul, mul_comm]

set_option exponentiation.threshold 300 in
/-- The square-root enclosure is accurate to `2^{-144}`: `√x ≤ s(x) + 2^{-144}`. -/
@[zeta5irr "lem_enc_sqrt"]
theorem sqrt_le_sqrtApprox_add {x : ℚ} (hx : 0 ≤ x) :
    √(x : ℝ) ≤ (sqrtApprox x : ℝ) + 2 ^ (-144 : ℤ) := by
  have h : ¬ ((sqrtApproxNum x + 1 : ℕ) : ℚ) ^ 2 ≤ 2 ^ 288 * x := by
    rw [sq_le_iff_le_sqrtApproxNum hx]
    omega
  have h' : 2 ^ 288 * (x : ℝ) < ((sqrtApproxNum x : ℝ) + 1) ^ 2 := by
    exact_mod_cast not_le.1 h
  have e : (sqrtApprox x : ℝ) + 2 ^ (-144 : ℤ) = ((sqrtApproxNum x : ℝ) + 1) / 2 ^ 144 := by
    rw [sqrtApprox, zpow_neg]
    push_cast
    ring
  rw [e, Real.sqrt_le_left (by positivity)]
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (x : ℝ) * (2 ^ 144) ^ 2 = 2 ^ 288 * (x : ℝ) := by rw [← pow_mul, mul_comm]
    _ ≤ _ := h'.le

end Zeta5Irr
