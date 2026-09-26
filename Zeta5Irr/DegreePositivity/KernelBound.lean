/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.DegreePositivity.Kernel
public import Mathlib.Algebra.Order.Star.Real

/-!
# A pointwise bound for the kernel `Ψ_b`

For `y ≥ 0` the kernel `Ψ_b(y) = (y⁵ - 10 b² y³ + 5 b⁴ y) / (y² + b²)⁵` satisfies
`|Ψ_b(y)| ≤ 16 y / (y² + b²)³`. By the triangle inequality the numerator is bounded in
absolute value by `y (y⁴ + 10 b² y² + 5 b⁴)`, and
`16 (y² + b²)² - (y⁴ + 10 b² y² + 5 b⁴) = 15 y⁴ + 22 b² y² + 11 b⁴ ≥ 0`.
The proof checks the two one-sided bounds on the numerator directly:
`16 y (y² + b²)² ∓ (y⁵ - 10 b² y³ + 5 b⁴ y)` equals `y (15 y⁴ + 42 b² y² + 11 b⁴)` or
`y (17 y⁴ + 22 b² y² + 21 b⁴)`, both nonnegative for `y ≥ 0`.

## Main results

* `Zeta5Irr.abs_weightKernel_le`: `|Ψ_b(y)| ≤ 16 y / (y² + b²)³` for `y ≥ 0`.

## Implementation notes

* The source states the bound for `b > 0` and `y > 0`. It holds for every real `b` and
  every `y ≥ 0`: at `y = b = 0` both sides are `0` under Lean's total division.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `y ≥ 0`, `|Ψ_b(y)| ≤ 16 y / (y² + b²)³`. -/
@[zeta5irr "lem_w_ker_bound"]
theorem abs_weightKernel_le (b : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |weightKernel b y| ≤ 16 * y / (y ^ 2 + b ^ 2) ^ 3 := by
  rcases (add_nonneg (sq_nonneg y) (sq_nonneg b)).eq_or_lt with hD | hD
  · rw [← hD]
    simp [weightKernel, ← hD]
  rw [weightKernel_def, abs_div, abs_of_pos (pow_pos hD 5),
    div_le_div_iff₀ (pow_pos hD 5) (pow_pos hD 3)]
  have key : |y ^ 5 - 10 * b ^ 2 * y ^ 3 + 5 * b ^ 4 * y| ≤ 16 * y * (y ^ 2 + b ^ 2) ^ 2 := by
    have h1 : 0 ≤ y * (17 * y ^ 4 + 22 * b ^ 2 * y ^ 2 + 21 * b ^ 4) := by positivity
    have h2 : 0 ≤ y * (15 * y ^ 4 + 42 * b ^ 2 * y ^ 2 + 11 * b ^ 4) := by positivity
    rw [abs_le]
    constructor <;> linarith
  calc |y ^ 5 - 10 * b ^ 2 * y ^ 3 + 5 * b ^ 4 * y| * (y ^ 2 + b ^ 2) ^ 3
      ≤ 16 * y * (y ^ 2 + b ^ 2) ^ 2 * (y ^ 2 + b ^ 2) ^ 3 := by gcongr
    _ = 16 * y * (y ^ 2 + b ^ 2) ^ 5 := by ring

end Zeta5Irr
