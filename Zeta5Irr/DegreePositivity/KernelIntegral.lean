/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.KernelSplit
public import Zeta5Irr.DegreePositivity.KernelIntegrable

/-!
# The integral of the kernel `Ψ_b` over `(0, ∞)`

For `b ≠ 0` we compute `∫₀^∞ Ψ_b(y) dy = 1 / (4 b⁴)`. Writing `q = y² + b²`, the function
`F(y) = -1 / (4 q²) + 2 b² / q³ - 2 b⁴ / q⁴`
has derivative `y / q³ - 12 b² y / q⁴ + 16 b⁴ y / q⁵`, which is `Ψ_b(y)` by the
partial-fraction decomposition of the kernel. Since `F(y) → 0` as `y → ∞`,
`F(0) = -1 / (4 b⁴)` and `Ψ_b` is integrable on `(0, ∞)`, the fundamental theorem of
calculus on the half-line gives the value.

## Main results

* `Zeta5Irr.integral_weightKernel_Ioi`: `∫₀^∞ Ψ_b(y) dy = 1 / (4 b⁴)` for `b ≠ 0`.

## Implementation notes

* The source states the result for `b > 0`; the proof only uses `b ≠ 0`.
* The antiderivative is written as a polynomial in `(y² + b²)⁻¹`, which makes both its
  derivative and its limit at infinity immediate.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Filter Topology

/-- For `b ≠ 0`, `∫₀^∞ Ψ_b(y) dy = 1 / (4 b⁴)`. -/
@[zeta5irr "lem_w_ker_int"]
theorem integral_weightKernel_Ioi {b : ℝ} (hb : b ≠ 0) :
    ∫ y in Set.Ioi 0, weightKernel b y = 1 / (4 * b ^ 4) := by
  have hq : ∀ y : ℝ, y ^ 2 + b ^ 2 ≠ 0 := fun y => by positivity
  set F : ℝ → ℝ := fun y =>
    -1 / 4 * ((y ^ 2 + b ^ 2)⁻¹) ^ 2 + 2 * b ^ 2 * ((y ^ 2 + b ^ 2)⁻¹) ^ 3
      - 2 * b ^ 4 * ((y ^ 2 + b ^ 2)⁻¹) ^ 4 with hF
  have hderiv : ∀ y : ℝ, HasDerivAt F (weightKernel b y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + b ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).add_const (b ^ 2)
    have h2 : HasDerivAt (fun y : ℝ => (y ^ 2 + b ^ 2)⁻¹) (-(2 * y) / (y ^ 2 + b ^ 2) ^ 2) y :=
      h1.inv (hq y)
    have h3 := ((h2.pow 2).const_mul (-1 / 4 : ℝ)).add
      ((h2.pow 3).const_mul (2 * b ^ 2)) |>.sub ((h2.pow 4).const_mul (2 * b ^ 4))
    convert h3 using 1
    rw [weightKernel_eq_split]
    have := hq y
    simp only [inv_pow]
    norm_num
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hinv : Tendsto (fun y : ℝ => (y ^ 2 + b ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp <|
        tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
    have := ((hinv.pow 2).const_mul (-1 / 4 : ℝ)).add
      ((hinv.pow 3).const_mul (2 * b ^ 2)) |>.sub ((hinv.pow 4).const_mul (2 * b ^ 4))
    convert this using 2
    norm_num
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun y _ => hderiv y) (integrableOn_weightKernel_Ioi hb) hlim]
  simp only [hF]
  field_simp
  ring

end Zeta5Irr
