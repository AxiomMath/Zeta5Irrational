/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExRAffine
public import Mathlib.Data.Finset.Slice

/-!
# The inner integral

Let `R = -Γ - 𝒩` be the inner limiting function. We evaluate its weighted integral exactly:
$$\int_3^{20} \frac{R(x)}{x^3}\,dx = \frac{322437603634266857629}{7535670527041937280000}.$$

Let `t₀ < t₁ < ⋯ < t₁₄₃` enumerate the breakpoint set `𝓔`, so that `t₀ = 3` and `t₁₄₃ = 20`.
On each open interval `(tᵢ, tᵢ₊₁)` the function `R` is affine, `R(x) = aᵢ x + bᵢ`, so
`R(x) / x³ = aᵢ x⁻² + bᵢ x⁻³` there and
`∫_{tᵢ}^{tᵢ₊₁} R(x) / x³ dx = aᵢ (tᵢ⁻¹ - tᵢ₊₁⁻¹) + (bᵢ / 2) (tᵢ⁻² - tᵢ₊₁⁻²)`
(the source's (B.3)). The coefficients `aᵢ`, `bᵢ` are the trisection slope and intercept of
`R`, which only involve values of `R` at rational points. At a rational point the closed forms
of `Γ` and `𝒩` are rational expressions in floors of rationals, so the sum of the `143`
contributions is a rational number that is computed exactly.

## Main definitions

* `Zeta5Irr.ratInnerLimitingR`: a computable function `ℚ → ℚ` agreeing with `R` on `ℚ`.
* `Zeta5Irr.exBreaksList`: the elements of `𝓔` in increasing order.
* `Zeta5Irr.exInnerTerm`: the contribution of the `k`-th interval of `𝓔` to the integral.

## Main results

* `Zeta5Irr.innerLimitingR_ratCast`: `R(x) = ratInnerLimitingR x` for rational `x`.
* `Zeta5Irr.orderEmbOfFin_exBreaks`: the increasing enumeration of `𝓔` is `exBreaksList`.
* `Zeta5Irr.intervalIntegrable_and_integral_affine_div_pow_three`:
  `∫_l^r (a x + b) / x³ dx = a (l⁻¹ - r⁻¹) + (b / 2) (l⁻² - r⁻²)` for `0 < l, r`.
* `Zeta5Irr.integral_innerLimitingR_div_pow_three`: the value of the inner integral.

## Implementation notes

* The source groups the `143` contributions by the integer part of `tᵢ` into seventeen
  partial sums over the unit intervals `[j, j + 1]`, `3 ≤ j ≤ 19`, before adding them. Here
  the `143` rational contributions are added directly, by evaluation in the kernel; the
  partial sums are not needed.
* The enumeration of `𝓔` is identified with the explicit list `exBreaksList` through
  `Finset.orderEmbOfFin_unique`: every entry lies in `𝓔` and the list is strictly increasing.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.3 (The inner integral), equation (B.3).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Set MeasureTheory

/-- The sign `e(u)` on the rationals: `1` if `u ≤ 1/2` and `-1` otherwise. -/
def ratEsign (u : ℚ) : ℚ := if u ≤ 1 / 2 then 1 else -1

/-- `ratEsign` computes `e` on the rationals. -/
theorem ratEsign_cast (u : ℚ) : ((ratEsign u : ℚ) : ℝ) = esign u := by
  have h : (u : ℝ) ≤ 1 / 2 ↔ u ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num, Rat.cast_le]
  simp only [ratEsign, esign, h]
  split_ifs <;> norm_num

/-- The distance `d₀(u) = min(u, 1 - u)` on the rationals. -/
def ratD₀ (u : ℚ) : ℚ := min u (1 - u)

/-- `ratD₀` computes `d₀` on the rationals. -/
theorem ratD₀_cast (u : ℚ) : ((ratD₀ u : ℚ) : ℝ) = d₀ u := by
  simp [ratD₀, d₀]

/-- The inner limiting function `R` on the rationals, through the closed forms of `Γ` and `𝒩`:
a computable function with `R(x) = ratInnerLimitingR x` for every rational `x`. -/
def ratInnerLimitingR (x : ℚ) : ℚ :=
  -((⌊2 * heightRatio * x⌋ - 6 * innerRatio * x) *
        (⌊2 * heightRatio * x⌋ + 6 * innerRatio * x - 2 * x - 5) / 2 -
      9 * (ratD₀ (Int.fract (innerRatio * x)) * (1 - 2 * ratD₀ (Int.fract (innerRatio * x)))) +
      3 * (ratEsign (Int.fract x) * ratEsign (Int.fract (innerRatio * x)) *
        (min (ratD₀ (Int.fract x)) (ratD₀ (Int.fract (innerRatio * x))) -
          2 * ratD₀ (Int.fract x) * ratD₀ (Int.fract (innerRatio * x)))) +
      (heightRatio * x - ⌊2 * heightRatio * x⌋ / 2) *
        (2 * ⌊2 * heightRatio * x⌋ - ⌊2 * x⌋ - 5) +
      max (heightRatio * x - ⌊2 * heightRatio * x⌋ / 2 - (2 * x - ⌊2 * x⌋) / 2) 0) -
    (2 * orderRatio * x * ⌊x⌋ - 12 * orderRatio * x * ⌊innerRatio * x⌋ -
      2 * (⌊2 * (orderRatio * x)⌋ * (orderRatio * x) -
        ⌊2 * (orderRatio * x)⌋ * (⌊2 * (orderRatio * x)⌋ + 1) / 4))

/-- `R(x) = ratInnerLimitingR x` for every rational `x`. -/
theorem innerLimitingR_ratCast (x : ℚ) : innerLimitingR x = ratInnerLimitingR x := by
  rw [innerLimitingR_def, innerLimitingGamma_eq, scalarLimitingFunction_def,
    innerLimitingFunction, allocationRemainder_def, baseHalfFract_def, basePoleCount_def,
    innerLimit_def, ratInnerLimitingR]
  push_cast [ratEsign_cast, ratD₀_cast, posPart_def]
  simp only [← Rat.floor_cast (α := ℝ)]
  push_cast
  rfl

/-- The breakpoints of `𝓔` in increasing order. -/
def exBreaksList : List ℚ :=
  [3, 70/23, 120/37, 140/43, 10/3, 80/23, 7/2, 160/43, 140/37, 90/23, 4, 180/43, 160/37, 100/23,
   9/2, 200/43, 110/23, 180/37, 5, 220/43, 120/23, 200/37, 11/2, 240/43, 130/23, 220/37, 6,
   260/43, 140/23, 240/37, 13/2, 280/43, 150/23, 20/3, 160/23, 300/43, 7, 260/37, 170/23, 320/43,
   15/2, 280/37, 180/23, 340/43, 8, 300/37, 190/23, 360/43, 17/2, 320/37, 200/23, 380/43, 9,
   210/23, 340/37, 400/43, 19/2, 220/23, 360/37, 420/43, 10, 440/43, 380/37, 240/23, 21/2,
   460/43, 400/37, 250/23, 11, 480/43, 260/23, 420/37, 23/2, 500/43, 270/23, 440/37, 12, 520/43,
   280/23, 460/37, 25/2, 540/43, 290/23, 480/37, 13, 560/43, 300/23, 40/3, 310/23, 580/43, 27/2,
   500/37, 320/23, 600/43, 14, 520/37, 330/23, 620/43, 29/2, 540/37, 340/23, 640/43, 15, 560/37,
   350/23, 660/43, 31/2, 360/23, 580/37, 680/43, 16, 370/23, 600/37, 700/43, 33/2, 380/23, 50/3,
   720/43, 620/37, 390/23, 17, 740/43, 640/37, 400/23, 35/2, 760/43, 410/23, 660/37, 18, 780/43,
   420/23, 680/37, 37/2, 800/43, 430/23, 700/37, 19, 820/43, 440/23, 720/37, 39/2, 840/43,
   450/23, 20]

/-- The increasing enumeration of `𝓔` is `exBreaksList`. -/
theorem orderEmbOfFin_exBreaks (i : Fin #exBreaks) :
    exBreaks.orderEmbOfFin rfl i = exBreaksList.getD i 0 := by
  have hmem : ∀ j : Fin 144, exBreaksList.getD j 0 ∈ exBreaks := by decide +kernel
  have hmono : StrictMono fun j : Fin 144 => exBreaksList.getD j 0 := by
    rw [Fin.strictMono_iff_lt_succ]
    decide +kernel
  have h := congrFun (orderEmbOfFin_unique card_exBreaks hmem hmono) ⟨i, card_exBreaks ▸ i.2⟩
  rw [orderEmbOfFin_apply] at h ⊢
  exact h.symm

/-- For `0 < l` and `0 < r`, the function `x ↦ (a x + b) / x³` is interval integrable on
`[l, r]`, with `∫_l^r (a x + b) / x³ dx = a (l⁻¹ - r⁻¹) + (b / 2) (l⁻² - r⁻²)`. -/
theorem intervalIntegrable_and_integral_affine_div_pow_three {a b l r : ℝ} (hl : 0 < l)
    (hr : 0 < r) :
    IntervalIntegrable (fun x => (a * x + b) / x ^ 3) volume l r ∧
      ∫ x in l..r, (a * x + b) / x ^ 3 = a * (l⁻¹ - r⁻¹) + b / 2 * ((l ^ 2)⁻¹ - (r ^ 2)⁻¹) := by
  have h0 : (0 : ℝ) ∉ uIcc l r := fun h => by
    rw [Set.mem_uIcc] at h
    rcases h with h | h <;> linarith [h.1]
  have hfun : (fun x : ℝ => (a * x + b) / x ^ 3) =
      fun x => a * x ^ (-2 : ℤ) + b * x ^ (-3 : ℤ) := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp only [zpow_neg, zpow_ofNat]
      field_simp
  have h2 := (intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -2)
    (Or.inr h0)).const_mul a
  have h3 := (intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -3)
    (Or.inr h0)).const_mul b
  rw [hfun]
  refine ⟨h2.add h3, ?_⟩
  rw [intervalIntegral.integral_add h2 h3, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩),
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  ring

/-- The contribution `aᵢ (tᵢ⁻¹ - tᵢ₊₁⁻¹) + (bᵢ / 2) (tᵢ⁻² - tᵢ₊₁⁻²)` of the `k`-th interval
`[tᵢ, tᵢ₊₁]` of `𝓔` to the inner integral, computed from the values of `R` at the two
trisection points. -/
def exInnerTerm (k : ℕ) : ℚ :=
  let l := exBreaksList.getD k 0
  let r := exBreaksList.getD (k + 1) 0
  let a := 3 / (r - l) * (ratInnerLimitingR ((l + 2 * r) / 3) -
    ratInnerLimitingR ((2 * l + r) / 3))
  let b := ratInnerLimitingR ((2 * l + r) / 3) - a * ((2 * l + r) / 3)
  a * (l⁻¹ - r⁻¹) + b / 2 * ((l ^ 2)⁻¹ - (r ^ 2)⁻¹)

/-- On the `k`-th interval `[tₖ, tₖ₊₁]` of `𝓔`, `x ↦ R(x) / x³` is interval integrable and its
integral is `exInnerTerm k`. -/
theorem intervalIntegrable_and_integral_innerLimitingR_div_pow_three_of_lt {k : ℕ}
    (hk : k < 143) :
    IntervalIntegrable (fun x => innerLimitingR x / x ^ 3) volume
        (exBreaksList.getD k 0 : ℝ) (exBreaksList.getD (k + 1) 0 : ℝ) ∧
      ∫ x in (exBreaksList.getD k 0 : ℝ)..(exBreaksList.getD (k + 1) 0 : ℝ),
        innerLimitingR x / x ^ 3 = exInnerTerm k := by
  have hi : k + 1 < #exBreaks := by rw [card_exBreaks]; omega
  have hl := orderEmbOfFin_exBreaks ⟨k, by omega⟩
  have hr := orderEmbOfFin_exBreaks ⟨k + 1, hi⟩
  simp only at hl hr
  have hlr : exBreaksList.getD k 0 < exBreaksList.getD (k + 1) 0 :=
    hl ▸ hr ▸ orderEmbOfFin_exBreaks_lt_succ hi
  have hl3 : (3 : ℚ) ≤ exBreaksList.getD k 0 :=
    (mem_Icc_of_mem_exBreaks (hl ▸ orderEmbOfFin_mem _ _ _)).1
  set l := exBreaksList.getD k 0
  set r := exBreaksList.getD (k + 1) 0
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by linarith : (0 : ℚ) < l)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by linarith : (0 : ℚ) < r)
  have hR : EqOn (fun x : ℝ => (exSlope hi * x + exIntercept hi) / x ^ 3)
      (fun x => innerLimitingR x / x ^ 3) (uIoo (l : ℝ) r) := by
    intro x hx
    rw [uIoo_of_le (by exact_mod_cast hlr.le)] at hx
    simp only
    rw [innerLimitingR_eq_exSlope_mul_add_exIntercept hi (by rw [hl]; exact hx.1)
      (by rw [hr]; exact hx.2)]
  have hp1 : ((l : ℝ) + 2 * r) / 3 = (((l + 2 * r) / 3 : ℚ) : ℝ) := by push_cast; ring
  have hp2 : (2 * (l : ℝ) + r) / 3 = (((2 * l + r) / 3 : ℚ) : ℝ) := by push_cast; ring
  have ha : exSlope hi = ((3 / (r - l) * (ratInnerLimitingR ((l + 2 * r) / 3) -
      ratInnerLimitingR ((2 * l + r) / 3)) : ℚ) : ℝ) := by
    rw [exSlope, trisectionSlope, hl, hr, hp1, hp2, innerLimitingR_ratCast,
      innerLimitingR_ratCast]
    push_cast
    ring
  have hb : exIntercept hi = ((ratInnerLimitingR ((2 * l + r) / 3) -
      3 / (r - l) * (ratInnerLimitingR ((l + 2 * r) / 3) -
        ratInnerLimitingR ((2 * l + r) / 3)) * ((2 * l + r) / 3) : ℚ) : ℝ) := by
    rw [exIntercept, trisectionIntercept, ← exSlope, ha, hl, hr, hp2, innerLimitingR_ratCast]
    push_cast
    ring
  obtain ⟨hint, heq⟩ := intervalIntegrable_and_integral_affine_div_pow_three
    (a := exSlope hi) (b := exIntercept hi) hl0 hr0
  refine ⟨hint.congr_uIoo hR, ?_⟩
  rw [← intervalIntegral.integral_congr_uIoo hR, heq, ha, hb, exInnerTerm]
  push_cast
  ring

/-- **The inner integral.** `∫₃²⁰ R(x) / x³ dx = 322437603634266857629 / 7535670527041937280000`.
-/
@[zeta5irr "lem_inner_integral"]
theorem integral_innerLimitingR_div_pow_three :
    ∫ x in (3 : ℝ)..20, innerLimitingR x / x ^ 3 =
      322437603634266857629 / 7535670527041937280000 := by
  have hsum : ∑ k ∈ range 143, exInnerTerm k =
      322437603634266857629 / 7535670527041937280000 := by
    decide +kernel
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => innerLimitingR x / x ^ 3) (μ := volume)
    (a := fun k => (exBreaksList.getD k 0 : ℝ)) (n := 143)
    fun k hk => (intervalIntegrable_and_integral_innerLimitingR_div_pow_three_of_lt hk).1
  have h3 : exBreaksList.getD 0 0 = 3 := rfl
  have h20 : exBreaksList.getD 143 0 = 20 := rfl
  simp only [h3, h20] at h
  push_cast at h
  rw [← h, Finset.sum_congr rfl fun k hk =>
    (intervalIntegrable_and_integral_innerLimitingR_div_pow_three_of_lt (mem_range.1 hk)).2,
    ← Rat.cast_sum, hsum]
  push_cast
  rfl

end Zeta5Irr
