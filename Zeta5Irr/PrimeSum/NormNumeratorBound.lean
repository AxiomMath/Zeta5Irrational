/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Sx
public import Zeta5Irr.LimitingFunctions.Nplus
public import Mathlib.Algebra.Order.Star.Real

/-!
# A bound on the numerator of the splitting of the inner limiting function

Write `τ = 2 s̃(x) = {2 H x}`, `ς = 2 ñ(x) = {2 x}` and `υ = {2 λ x}`, all three in `[0, 1)`.
The numerator appearing in the splitting of the inner limiting function is
`τ (τ - ς) - (τ - ς)₊ + υ (1 - υ)`, and it lies in `[-1/4, 1/4]`.

Indeed `υ (1 - υ) = 1/4 - (υ - 1/2)²` lies in `[0, 1/4]`, while
`N₁ = τ (τ - ς) - (τ - ς)₊` lies in `[-1/4, 0]`: if `τ ≥ ς` then `N₁ = (τ - ς)(τ - 1)`, and
`0 ≤ (τ - ς)(1 - τ) ≤ τ (1 - τ) ≤ 1/4`; if `τ < ς` then `N₁ = τ (τ - ς)` and
`0 ≤ τ (ς - τ) ≤ τ (1 - τ) ≤ 1/4`.

## Main results

* `Zeta5Irr.numerator_bound_of_mem_Ico`: the bound for arbitrary `τ, ς ∈ [0, 1)` and
  `υ ∈ [0, 1]`.
* `Zeta5Irr.normNumerator_bound`: the bound for `τ = 2 s̃(x)`, `ς = 2 ñ(x)`, `υ = {2 λ x}`.

## Implementation notes

* The source states the bound for `x ≥ 3`; it holds for every real `x`, since it only uses
  that `τ, ς, υ` are fractional parts, so the restriction is dropped.
* The two-sided bound is stated as `-1/4 ≤ N ∧ N ≤ 1/4`, as in the source.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.5 (The splitting of the inner limiting function).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `τ, ς ∈ [0, 1)` and `υ ∈ [0, 1]`,
`-1/4 ≤ τ (τ - ς) - (τ - ς)₊ + υ (1 - υ) ≤ 1/4`. -/
theorem numerator_bound_of_mem_Ico {τ ς υ : ℝ} (hτ : τ ∈ Set.Ico 0 1) (hς : ς ∈ Set.Ico 0 1)
    (hυ : υ ∈ Set.Icc 0 1) :
    -(1 / 4) ≤ τ * (τ - ς) - (τ - ς)⁺ + υ * (1 - υ) ∧
      τ * (τ - ς) - (τ - ς)⁺ + υ * (1 - υ) ≤ 1 / 4 := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨hς0, hς1⟩ := hς
  obtain ⟨hυ0, hυ1⟩ := hυ
  have hN₂ : 0 ≤ υ * (1 - υ) := mul_nonneg hυ0 (by linarith)
  have hN₂' : υ * (1 - υ) ≤ 1 / 4 := by nlinarith [sq_nonneg (υ - 1 / 2)]
  have hτq : τ * (1 - τ) ≤ 1 / 4 := by nlinarith [sq_nonneg (τ - 1 / 2)]
  rcases le_or_gt ς τ with h | h
  · rw [posPart_eq_self.2 (sub_nonneg.2 h)]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hτ1.le)]
  · rw [posPart_eq_zero.2 (sub_nonpos.2 h.le)]
    constructor <;> nlinarith [mul_nonneg hτ0 (sub_nonneg.2 h.le)]

/-- **The numerator bound.** For every real `x` (the source takes `x ≥ 3`),
`-1/4 ≤ 2 s̃(x) (2 s̃(x) - 2 ñ(x)) - (2 s̃(x) - 2 ñ(x))₊ + {2 λ x} (1 - {2 λ x}) ≤ 1/4`. -/
@[zeta5irr "lem_norm_numerator_bound"]
theorem normNumerator_bound (x : ℝ) :
    -(1 / 4) ≤ 2 * allocationRemainder x * (2 * allocationRemainder x - 2 * baseHalfFract x) -
        (2 * allocationRemainder x - 2 * baseHalfFract x)⁺ +
        Int.fract (2 * (orderRatio : ℝ) * x) * (1 - Int.fract (2 * (orderRatio : ℝ) * x)) ∧
      2 * allocationRemainder x * (2 * allocationRemainder x - 2 * baseHalfFract x) -
        (2 * allocationRemainder x - 2 * baseHalfFract x)⁺ +
        Int.fract (2 * (orderRatio : ℝ) * x) * (1 - Int.fract (2 * (orderRatio : ℝ) * x)) ≤
        1 / 4 := by
  refine numerator_bound_of_mem_Ico ?_ ?_ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · rw [allocationRemainder_eq_half_fract, mul_div_cancel₀ _ two_ne_zero]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · rw [baseHalfFract_eq_fract, mul_div_cancel₀ _ two_ne_zero]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

end Zeta5Irr
