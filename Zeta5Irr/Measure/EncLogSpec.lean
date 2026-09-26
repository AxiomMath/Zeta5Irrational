/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.EncLog
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star

/-!
# The two-sided enclosure of the logarithm by `Λ_m`

For `0 ≤ z < 1` and `m : ℕ`, the partial sum `Λ_m(z) = 2 ∑_{k<m} z^{2k+1} / (2k+1)` of the
series `log ((1 + z) / (1 - z)) = 2 ∑_{k ≥ 0} z^{2k+1} / (2k+1)` satisfies
`0 ≤ log ((1 + z) / (1 - z)) - Λ_m(z) ≤ 2 z^{2m+1} / ((2m+1) (1 - z²))`.
The difference is the tail `2 ∑_{k ≥ m} z^{2k+1} / (2k+1)`; its terms are nonnegative, and
bounding `1 / (2k+1)` by `1 / (2m+1)` leaves a geometric series in `z²`.

## Main results

* `Zeta5Irr.log_sub_logApprox_nonneg`: `0 ≤ log ((1 + z) / (1 - z)) - Λ_m(z)`.
* `Zeta5Irr.log_sub_logApprox_le`:
  `log ((1 + z) / (1 - z)) - Λ_m(z) ≤ 2 z^{2m+1} / ((2m+1) (1 - z²))`.
* `Zeta5Irr.log_div_mem_logApprox`: both bounds together, as an enclosure of
  `log ((1 + z) / (1 - z))`.
* `Zeta5Irr.hasSum_log_sub_logApprox`: the difference is the tail of the series.

## Implementation notes

* The source assumes `m ≥ 1`; both bounds hold for `m = 0` too, where `Λ_0 = 0`, so the
  hypothesis is dropped.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `|z| < 1`, `log ((1 + z) / (1 - z)) - Λ_m(z)` is the tail
`∑_{n ≥ 0} 2 z^{2(n+m)+1} / (2(n+m)+1)` of the series of the logarithm. -/
theorem hasSum_log_sub_logApprox {z : ℝ} (h : |z| < 1) (m : ℕ) :
    HasSum (fun n : ℕ => 2 * (z ^ (2 * (n + m) + 1) / (2 * ((n + m : ℕ) : ℝ) + 1)))
      (Real.log ((1 + z) / (1 - z)) - logApprox m z) := by
  have h₁ : 0 < 1 + z := by linarith [neg_abs_le z]
  have h₂ : 0 < 1 - z := by linarith [le_abs_self z]
  have hs := (hasSum_nat_add_iff' m).2 (Real.hasSum_log_sub_log_of_abs_lt_one h)
  rw [← Real.log_div h₁.ne' h₂.ne'] at hs
  convert hs using 1
  · ext n
    ring
  · simp only [logApprox, mul_sum]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    ring

/-- For `0 ≤ z < 1`, `Λ_m(z) ≤ log ((1 + z) / (1 - z))`. -/
@[zeta5irr "lem_enc_log"]
theorem log_sub_logApprox_nonneg {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    0 ≤ Real.log ((1 + z) / (1 - z)) - logApprox m z :=
  sub_nonneg.2 (logApprox_le_log h₀ h₁ m)

/-- For `0 ≤ z < 1`, `log ((1 + z) / (1 - z)) - Λ_m(z) ≤ 2 z^{2m+1} / ((2m+1) (1 - z²))`. -/
@[zeta5irr "lem_enc_log"]
theorem log_sub_logApprox_le {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    Real.log ((1 + z) / (1 - z)) - logApprox m z ≤
      2 * z ^ (2 * m + 1) / ((2 * m + 1) * (1 - z ^ 2)) := by
  have habs : |z| < 1 := by rwa [abs_of_nonneg h₀]
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hm : (0 : ℝ) < 2 * m + 1 := by positivity
  have hgeom : HasSum (fun n : ℕ => 2 * z ^ (2 * m + 1) / (2 * m + 1) * (z ^ 2) ^ n)
      (2 * z ^ (2 * m + 1) / (2 * m + 1) * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left _
  have key : 2 * z ^ (2 * m + 1) / ((2 * m + 1) * (1 - z ^ 2)) =
      2 * z ^ (2 * m + 1) / (2 * m + 1) * (1 - z ^ 2)⁻¹ := by
    field_simp
  rw [key]
  refine hasSum_le (fun n => ?_) (hasSum_log_sub_logApprox habs m) hgeom
  have e : 2 * z ^ (2 * m + 1) / (2 * m + 1) * (z ^ 2) ^ n =
      2 * (z ^ (2 * (n + m) + 1) / (2 * m + 1)) := by
    rw [← pow_mul, show 2 * (n + m) + 1 = 2 * m + 1 + 2 * n by ring, pow_add]
    ring
  rw [e]
  gcongr
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The logarithm `log ((1 + z) / (1 - z))` lies between `Λ_m(z)` and
`Λ_m(z) + 2 z^{2m+1} / ((2m+1) (1 - z²))`, for `0 ≤ z < 1`. -/
theorem log_div_mem_logApprox {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    logApprox m z ≤ Real.log ((1 + z) / (1 - z)) ∧
      Real.log ((1 + z) / (1 - z)) ≤
        logApprox m z + 2 * z ^ (2 * m + 1) / ((2 * m + 1) * (1 - z ^ 2)) := by
  have := log_sub_logApprox_nonneg h₀ h₁ m
  have := log_sub_logApprox_le h₀ h₁ m
  constructor <;> linarith

end Zeta5Irr
