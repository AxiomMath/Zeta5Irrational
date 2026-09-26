/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Kernel
public import Mathlib.Algebra.Order.Star.Real

/-!
# Partial fractions of the kernel `Ψ_b`

Writing `q = y² + b²`, the numerator of the kernel `Ψ_b(y) = (y⁵ - 10 b² y³ + 5 b⁴ y) / q⁵`
factors as `y (q² - 12 b² q + 16 b⁴)`, so that
`Ψ_b(y) = y / q³ - 12 b² y / q⁴ + 16 b⁴ y / q⁵`.

## Main results

* `Zeta5Irr.weightKernel_eq_split`: the decomposition
  `Ψ_b(y) = y / (y² + b²)³ - 12 b² y / (y² + b²)⁴ + 16 b⁴ y / (y² + b²)⁵`.

## Implementation notes

* The source states the decomposition for `b > 0`. It holds for every real `b` and `y`:
  the only point where `y² + b² = 0` is `y = b = 0`, where both sides vanish.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- The partial-fraction decomposition
`Ψ_b(y) = y / (y² + b²)³ - 12 b² y / (y² + b²)⁴ + 16 b⁴ y / (y² + b²)⁵`. -/
@[zeta5irr "lem_w_ker_split"]
theorem weightKernel_eq_split (b y : ℝ) :
    weightKernel b y = y / (y ^ 2 + b ^ 2) ^ 3 - 12 * b ^ 2 * y / (y ^ 2 + b ^ 2) ^ 4
      + 16 * b ^ 4 * y / (y ^ 2 + b ^ 2) ^ 5 := by
  rw [weightKernel_def]
  by_cases h : y ^ 2 + b ^ 2 = 0
  · have hy : y = 0 := by nlinarith [sq_nonneg y, sq_nonneg b]
    simp [hy]
  · field_simp
    ring

end Zeta5Irr
