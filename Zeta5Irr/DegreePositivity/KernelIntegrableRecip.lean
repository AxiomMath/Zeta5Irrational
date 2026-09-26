/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Kernel
public import Zeta5Irr.DegreePositivity.KernelBound
public import Zeta5Irr.DegreePositivity.PowIntegrable
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Integrability of `Ψ_b(y) / y` on `(0, ∞)`

For a real `b ≠ 0` the function `y ↦ Ψ_b(y) / y` is integrable on `(0, ∞)`. It is continuous
there, and dividing the bound `|Ψ_b(y)| ≤ 16 y / (y² + b²)³` by `y > 0` dominates it by
`16 (y² + b²)⁻³`, which is integrable on `(0, ∞)`.

## Main results

* `Zeta5Irr.integrableOn_weightKernel_div_self`: `y ↦ Ψ_b(y) / y` is integrable on `(0, ∞)`.

## Implementation notes

* The source assumes `b > 0`; the argument only uses `b ≠ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory

namespace Zeta5Irr

/-- For `b ≠ 0`, the function `y ↦ Ψ_b(y) / y` is integrable on `(0, ∞)`. -/
@[zeta5irr "lem_w_ker_integrable_recip"]
theorem integrableOn_weightKernel_div_self {b : ℝ} (hb : b ≠ 0) :
    IntegrableOn (fun y => weightKernel b y / y) (Set.Ioi 0) := by
  refine ((integrableOn_inv_sq_add_sq_pow hb (m := 3) (by norm_num)).const_mul 16).mono' ?_ ?_
  · exact ((continuous_weightKernel hb).continuousOn.div continuousOn_id
      fun y hy => ne_of_gt hy).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy, div_le_iff₀ hy]
    calc |weightKernel b y| ≤ 16 * y / (y ^ 2 + b ^ 2) ^ 3 := abs_weightKernel_le b hy.le
      _ = 16 * ((y ^ 2 + b ^ 2) ^ 3)⁻¹ * y := by rw [div_eq_mul_inv]; ring

end Zeta5Irr
