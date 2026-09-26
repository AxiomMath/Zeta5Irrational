/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormG0
public import Mathlib.Algebra.Order.Star.Real

/-!
# The maximum of the cubic kernel on the unit interval

The cubic kernel `G₀(v) = v (1 - v) (2v - 1) / 6` satisfies
`max_{v ∈ [0, 1]} |G₀(v)| = 1 / (36 √3)`, the maximum being attained at the critical points
`v_± = (1 ± 1/√3) / 2`.

## Main results

* `Zeta5Irr.abs_cubicKernel_le`: `|G₀(v)| ≤ 1 / (36 √3)` for `v ∈ [0, 1]`.
* `Zeta5Irr.isGreatest_abs_cubicKernel`: `1 / (36 √3)` is the greatest value of `|G₀|` on
  `[0, 1]`.

## Implementation notes

* Instead of locating the critical points of `G₀`, the bound is proved algebraically: writing
  `t = v (1 - v)`, one has `(2v - 1)² = 1 - 4t`, hence `36 G₀(v)² = t² (1 - 4t)`, and
  `1 - 108 t² + 432 t³ = (6t - 1)² (12t + 1) ≥ 0` for `t ≥ 0`. Equality holds at
  `v = (1 - 1/√3) / 2`, where `t = 1/6`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open Set Real

/-- On `[0, 1]` the cubic kernel is bounded by `1 / (36 √3)`: `|G₀(v)| ≤ 1 / (36 √3)`. -/
theorem abs_cubicKernel_le {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    |cubicKernel v| ≤ 1 / (36 * √3) := by
  obtain ⟨h0, h1⟩ := hv
  have hs : (0 : ℝ) < √3 := by positivity
  have hs2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (0 : ℝ) ≤ 1 / (36 * √3) := by positivity
  rw [← abs_of_nonneg hc, ← sq_le_sq, div_pow, mul_pow, hs2]
  set t := v * (1 - v) with ht
  have ht0 : 0 ≤ t := mul_nonneg h0 (by linarith)
  have key : cubicKernel v ^ 2 = t ^ 2 * (1 - 4 * t) / 36 := by
    rw [ht]; unfold cubicKernel; ring
  rw [key, div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith [mul_nonneg (sq_nonneg (6 * t - 1)) (by linarith : (0 : ℝ) ≤ 12 * t + 1)]

/-- **The maximum of `|G₀|` on `[0, 1]`**: `max_{v ∈ [0, 1]} |G₀(v)| = 1 / (36 √3)`. -/
@[zeta5irr "lem_norm_G0_max"]
theorem isGreatest_abs_cubicKernel :
    IsGreatest ((fun v => |cubicKernel v|) '' Icc 0 1) (1 / (36 * √3)) := by
  refine ⟨⟨(1 - 1 / √3) / 2, ?_, ?_⟩, ?_⟩
  · have hs : (1 : ℝ) ≤ √3 := Real.one_le_sqrt.mpr (by norm_num)
    have h : 1 / √3 ≤ 1 := by rw [div_le_one (by positivity)]; exact hs
    have h' : 0 ≤ 1 / √3 := by positivity
    constructor <;> linarith
  · have hs : (0 : ℝ) < √3 := by positivity
    have hs2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have : cubicKernel ((1 - 1 / √3) / 2) = -(1 / (36 * √3)) := by
      unfold cubicKernel
      field_simp
      linear_combination (-12 : ℝ) * hs2
    simp only [this, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (36 * √3))]
  · rintro _ ⟨v, hv, rfl⟩
    exact abs_cubicKernel_le hv

end Zeta5Irr
