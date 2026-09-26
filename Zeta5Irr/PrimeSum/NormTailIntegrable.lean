/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.QBounds
public import Zeta5Irr.PrimeSum.NormQLower
public import Zeta5Irr.PrimeSum.NormRPwc
public import Zeta5Irr.PrimeSum.NormPntOuter

/-!
# Integrability of the tail of `R(x) / x³`

For every real `x₀ > 0`, and in particular for every `x₀ ≥ 3`, the function `x ↦ R(x) / x³`
is integrable on `[x₀, ∞)`, where `R` is the inner limiting function.

By the splitting `R(x) = x Φ(x) + 𝓔(x)`, with `|Φ(x)| ≤ 18` and `-1/2 ≤ 𝓔(x) ≤ 13/8`, one has
`|R(x) / x³| ≤ 18 x⁻² + (13/8) x⁻³` for `x > 0`, and the right-hand side is integrable on
`(x₀, ∞)`. Measurability on `(x₀, ∞)` follows from the piecewise continuity of `R` on each
bounded interval `[x₀, x₀ + n + 1]`, which makes it integrable there.

## Main results

* `Zeta5Irr.integrableOn_innerLimitingR_div_pow_three_Ici`: `x ↦ R(x) / x³` is integrable on
  `[x₀, ∞)` for every `x₀ > 0`.

## Implementation notes

* The source states the result for `x₀ ≥ 3`. The bounds on `Φ` and `𝓔` hold for all real `x`
  and the piecewise continuity of `R` for all intervals, so only `x₀ > 0` is needed, for the
  integrability of the dominating function `18 x⁻² + (13/8) x⁻³`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- `x ↦ R(x) / x³` is almost everywhere strongly measurable on `(x₀, ∞)`. -/
theorem aestronglyMeasurable_innerLimitingR_div_pow_three_Ioi (x₀ : ℝ) :
    AEStronglyMeasurable (fun x => innerLimitingR x / x ^ 3) (volume.restrict (Ioi x₀)) := by
  have hU : Ioi x₀ = ⋃ n : ℕ, Ioc x₀ (x₀ + (n + 1)) := by
    ext x
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    refine ⟨fun hx => ?_, fun ⟨_, hx, _⟩ => hx⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (x - x₀)
    exact ⟨n, hx, by linarith⟩
  rw [hU, aestronglyMeasurable_iUnion_iff]
  intro n
  have hlt : x₀ < x₀ + (n + 1) := by linarith [n.cast_nonneg (α := ℝ)]
  have hR : IntervalIntegrable innerLimitingR volume x₀ (x₀ + (n + 1)) :=
    (piecewiseContinuousOn_innerLimitingR hlt).intervalIntegrable
  have hR' := hR.1.aestronglyMeasurable
  exact hR'.mul (by fun_prop : Measurable fun x : ℝ => (x ^ 3)⁻¹).aestronglyMeasurable

/-- For `x > 0`, `|R(x) / x³| ≤ 18 x⁻² + (13/8) x⁻³`. -/
theorem abs_innerLimitingR_div_pow_three_le {x : ℝ} (hx : 0 < x) :
    |innerLimitingR x / x ^ 3| ≤ 18 * x ^ (-2 : ℝ) + 13 / 8 * x ^ (-3 : ℝ) := by
  have h2 : x ^ (-2 : ℝ) = x / x ^ 3 := by
    rw [Real.rpow_neg hx.le, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    field_simp
  have h3 : x ^ (-3 : ℝ) = 1 / x ^ 3 := by
    rw [Real.rpow_neg hx.le, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
    simp
  have hx3 : 0 < x ^ 3 := by positivity
  rw [h2, h3, innerLimitingR_eq, abs_div, abs_of_pos hx3, div_le_iff₀ hx3]
  have hΦ := abs_sawtoothSlope_le_eighteen x
  have hE₁ := innerSplitError_le x
  have hE₂ := neg_half_le_innerSplitError x
  have hE : |innerSplitError x| ≤ 13 / 8 := abs_le.2 ⟨by linarith, hE₁⟩
  calc |x * sawtoothSlope x + innerSplitError x|
      ≤ x * |sawtoothSlope x| + |innerSplitError x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hx]
    _ ≤ x * 18 + 13 / 8 := by gcongr
    _ = (18 * (x / x ^ 3) + 13 / 8 * (1 / x ^ 3)) * x ^ 3 := by field_simp

/-- **Integrability of the tail.** For every real `x₀ > 0` (the source takes `x₀ ≥ 3`), the
function `x ↦ R(x) / x³` is integrable on `[x₀, ∞)`. -/
@[zeta5irr "lem_norm_tail_integrable"]
theorem integrableOn_innerLimitingR_div_pow_three_Ici {x₀ : ℝ} (hx₀ : 0 < x₀) :
    IntegrableOn (fun x => innerLimitingR x / x ^ 3) (Ici x₀) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hg : IntegrableOn (fun x : ℝ => 18 * x ^ (-2 : ℝ) + 13 / 8 * x ^ (-3 : ℝ)) (Ioi x₀) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx₀).const_mul 18).add
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) hx₀).const_mul (13 / 8))
  refine hg.mono' (aestronglyMeasurable_innerLimitingR_div_pow_three_Ioi x₀) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Real.norm_eq_abs]
  exact abs_innerLimitingR_div_pow_three_le (hx₀.trans hx)

end Zeta5Irr
