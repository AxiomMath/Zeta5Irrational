/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Kernel
public import Zeta5Irr.DegreePositivity.KernelSplit
public import Zeta5Irr.DegreePositivity.PowIntegral

/-!
# The integral of `Ψ_b(y) / y` over `(0, ∞)`

For a real `b > 0`,
`∫₀^∞ Ψ_b(y) / y dy = π / (2 b⁵)`.

Dividing the partial fraction splitting of `Ψ_b(y)` by `y > 0` gives
`Ψ_b(y) / y = (y² + b²)⁻³ - 12 b² (y² + b²)⁻⁴ + 16 b⁴ (y² + b²)⁻⁵`,
each term is integrable on `(0, ∞)`, and the three integrals are
`3π / (16 b⁵)`, `5π / (32 b⁷)` and `35π / (256 b⁹)`. Combining them gives
`π / b⁵ · (3/16 - 15/8 + 35/16) = π / (2 b⁵)`.

## Main results

* `Zeta5Irr.integral_weightKernel_div_self`: `∫₀^∞ Ψ_b(y) / y dy = π / (2 b⁵)` for `b > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Real

namespace Zeta5Irr

/-- For `b > 0`, `∫₀^∞ Ψ_b(y) / y dy = π / (2 b⁵)`. -/
@[zeta5irr "lem_w_ker_recip"]
theorem integral_weightKernel_div_self {b : ℝ} (hb : 0 < b) :
    ∫ y in Set.Ioi 0, weightKernel b y / y = π / (2 * b ^ 5) := by
  have hsplit : ∀ y ∈ Set.Ioi (0 : ℝ), weightKernel b y / y =
      ((y ^ 2 + b ^ 2) ^ 3)⁻¹ - 12 * b ^ 2 * ((y ^ 2 + b ^ 2) ^ 4)⁻¹
        + 16 * b ^ 4 * ((y ^ 2 + b ^ 2) ^ 5)⁻¹ := by
    intro y (hy : 0 < y)
    have hq : 0 < y ^ 2 + b ^ 2 := by positivity
    rw [weightKernel_eq_split]
    field_simp
  have hi : ∀ m, 1 ≤ m → IntegrableOn (fun y : ℝ => ((y ^ 2 + b ^ 2) ^ m)⁻¹) (Set.Ioi 0) :=
    fun m hm => integrableOn_inv_sq_add_sq_pow hb.ne' hm
  have h3 := hi 3 (by norm_num)
  have h4 : IntegrableOn (fun y : ℝ => 12 * b ^ 2 * ((y ^ 2 + b ^ 2) ^ 4)⁻¹) (Set.Ioi 0) :=
    (hi 4 (by norm_num)).const_mul _
  have h5 : IntegrableOn (fun y : ℝ => 16 * b ^ 4 * ((y ^ 2 + b ^ 2) ^ 5)⁻¹) (Set.Ioi 0) :=
    (hi 5 (by norm_num)).const_mul _
  have h34 : IntegrableOn (fun y : ℝ =>
      ((y ^ 2 + b ^ 2) ^ 3)⁻¹ - 12 * b ^ 2 * ((y ^ 2 + b ^ 2) ^ 4)⁻¹) (Set.Ioi 0) :=
    h3.sub h4
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add h34 h5,
    integral_sub h3 h4,
    integral_const_mul, integral_const_mul,
    integral_Ioi_inv_sq_add_sq_pow hb (by norm_num : 1 ≤ 3),
    integral_Ioi_inv_sq_add_sq_pow hb (by norm_num : 1 ≤ 4),
    integral_Ioi_inv_sq_add_sq_pow hb (by norm_num : 1 ≤ 5)]
  norm_num [Nat.choose]
  field_simp
  ring

end Zeta5Irr
