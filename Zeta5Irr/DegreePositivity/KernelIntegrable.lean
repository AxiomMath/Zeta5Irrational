/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.DegreePositivity.KernelBound
public import Zeta5Irr.DegreePositivity.PowIntegrable
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Integrability of the kernel `Ψ_b` on `(0, ∞)`

For `b ≠ 0` the kernel `Ψ_b(y) = (y⁵ - 10 b² y³ + 5 b⁴ y) / (y² + b²)⁵` is Lebesgue
integrable, hence absolutely integrable, on `(0, ∞)`. It is continuous, and for `y > 0`
the pointwise bound `|Ψ_b(y)| ≤ 16 y / (y² + b²)³` together with `2 |b| y ≤ y² + b²`
gives `|Ψ_b(y)| ≤ (8 / |b|) (y² + b²)⁻²`, which is integrable on `(0, ∞)`.

## Main results

* `Zeta5Irr.integrableOn_weightKernel_Ioi`: `Ψ_b` is integrable on `(0, ∞)` for `b ≠ 0`.

## Implementation notes

* The source states the result for `b > 0`; the proof only uses `b ≠ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- For `b ≠ 0`, the kernel `Ψ_b` is (absolutely) integrable on `(0, ∞)`. -/
@[zeta5irr "lem_w_ker_integrable"]
theorem integrableOn_weightKernel_Ioi {b : ℝ} (hb : b ≠ 0) :
    IntegrableOn (weightKernel b) (Set.Ioi 0) := by
  refine ((integrableOn_inv_sq_add_sq_pow hb (m := 2) (by norm_num)).const_mul
    (8 / |b|)).mono' (continuous_weightKernel hb).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  have hab : 0 < |b| := abs_pos.2 hb
  have hD : 0 < y ^ 2 + b ^ 2 := by positivity
  have h2 : 2 * |b| * y ≤ y ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (y - |b|), sq_abs b]
  rw [Real.norm_eq_abs]
  refine (abs_weightKernel_le b hy.le).trans ?_
  rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, ← div_eq_mul_inv,
    div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : 0 < (y ^ 2 + b ^ 2) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 this.le]

end Zeta5Irr
