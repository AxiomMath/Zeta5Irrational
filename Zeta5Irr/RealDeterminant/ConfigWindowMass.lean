/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotParam
public import Mathlib.Tactic.ENatToNat

/-!
# The mass of a window under the arcsine measure

For reals `a < b`, the arcsine measure `ω_{[a,b]}` gives every open interval `(c - r, c + r)`
at most the mass `2 √(r / (b - a))`, uniformly in the centre `c`.

Along the parametrisation `θ ↦ (a + b)/2 + (b - a)/2 cos θ` of `(a, b)` by the half-circle
`(0, π)`, the measure `ω_{[a,b]}` is `π⁻¹` times Lebesgue measure. The window pulls back to the
set of angles `θ` with `α < cos θ < β`, where `β - α = 4r/(b - a)`, and this set lies in the
interval `[arccos β, arccos α]`. It remains to bound the length of an interval of angles
`[φ₁, φ₂] ⊆ [0, π]` by the difference of cosines at its ends: by the sum-to-product formula
`cos φ₁ - cos φ₂ = 2 sin ((φ₁ + φ₂)/2) sin ((φ₂ - φ₁)/2)`, and Jordan's inequality bounds both
sines below by `(φ₂ - φ₁)/π`, so `φ₂ - φ₁ ≤ π √(cos φ₁ - cos φ₂)`.

## Main results

* `Zeta5Irr.sub_le_pi_mul_sqrt_cos_sub_cos`: `φ₂ - φ₁ ≤ π √(cos φ₁ - cos φ₂)` for
  `0 ≤ φ₁ ≤ φ₂ ≤ π`.
* `Zeta5Irr.arcsineMeasure_Ioo_le`: `ω_{[a,b]}((c - r, c + r)) ≤ 2 √(r / (b - a))`.
* `Zeta5Irr.measureReal_arcsineMeasure_Ioo_le`: the same bound for the real-valued mass.

## Implementation notes

* The source splits the window at the midpoint `(a + b)/2`, moves each half to the nearer
  endpoint using the monotonicity of the arcsine density on either side of the midpoint, and
  applies the endpoint bound `ω_{[a,b]}([a, a + y]) ≤ √(y / (b - a))` to each half. Here the
  bound is read off instead from the parametrisation of `ω_{[a,b]}` by the half-circle, which
  reduces it to an inequality between an angle and a difference of cosines; the constant `2`
  is the same.
* The hypothesis `0 < r` of the source is dropped: for `r ≤ 0` the window is empty.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real
open scoped ENNReal

/-- For `0 ≤ x ≤ π` and `0 ≤ y ≤ min x (π - x)`, Jordan's inequality gives
`(2/π) y ≤ sin x`. -/
lemma two_div_pi_mul_le_sin_of_le {x y : ℝ} (hy : 0 ≤ y) (hx : y ≤ x) (hx' : y ≤ π - x) :
    2 / π * y ≤ sin x := by
  have hπ := pi_pos
  rcases le_or_gt x (π / 2) with h | h
  · calc 2 / π * y ≤ 2 / π * x := by gcongr
      _ ≤ sin x := mul_le_sin (hy.trans hx) h
  · calc 2 / π * y ≤ 2 / π * (π - x) := by gcongr
      _ ≤ sin (π - x) := mul_le_sin (hy.trans hx') (by linarith)
      _ = sin x := sin_pi_sub x

/-- The length of an interval of angles `[φ₁, φ₂] ⊆ [0, π]` is at most `π` times the square root
of the difference of the cosines at its ends. -/
lemma sub_le_pi_mul_sqrt_cos_sub_cos {φ₁ φ₂ : ℝ} (h₀ : 0 ≤ φ₁) (h₁₂ : φ₁ ≤ φ₂) (hπ : φ₂ ≤ π) :
    φ₂ - φ₁ ≤ π * √(cos φ₁ - cos φ₂) := by
  have hpi := pi_pos
  set δ := φ₂ - φ₁ with hδ
  have hδ0 : 0 ≤ δ := sub_nonneg.2 h₁₂
  have hs : δ / π ≤ sin ((φ₁ + φ₂) / 2) := by
    have := two_div_pi_mul_le_sin_of_le (x := (φ₁ + φ₂) / 2) (y := δ / 2) (by linarith)
      (by linarith) (by linarith)
    convert this using 1
    field_simp
  have hd : δ / π ≤ sin (δ / 2) := by
    have := two_div_pi_mul_le_sin_of_le (x := δ / 2) (y := δ / 2) (by linarith) le_rfl
      (by linarith)
    convert this using 1
    field_simp
  have hq : 0 ≤ δ / π := div_nonneg hδ0 hpi.le
  have hcos : cos φ₁ - cos φ₂ = 2 * sin ((φ₁ + φ₂) / 2) * sin (δ / 2) := by
    rw [cos_sub_cos, show (φ₁ - φ₂) / 2 = -(δ / 2) by rw [hδ]; ring, sin_neg]
    ring
  have hnn : 0 ≤ cos φ₁ - cos φ₂ := by
    rw [hcos]
    exact mul_nonneg (mul_nonneg zero_le_two (hq.trans hs)) (hq.trans hd)
  have key : δ / π ≤ √(cos φ₁ - cos φ₂) := by
    rw [le_sqrt hq hnn, hcos]
    nlinarith [mul_le_mul hs hd hq (hq.trans hs)]
  rw [div_le_iff₀ hpi] at key
  linarith

/-- For `-1 < β`, `cos (arccos β) ≤ β`. -/
lemma cos_arccos_le {β : ℝ} (hβ : -1 < β) : cos (arccos β) ≤ β := by
  rcases le_or_gt β 1 with h | h
  · rw [cos_arccos hβ.le h]
  · rw [arccos_of_one_le h.le, cos_zero]
    exact h.le

/-- For `α < 1`, `α ≤ cos (arccos α)`. -/
lemma le_cos_arccos {α : ℝ} (hα : α < 1) : α ≤ cos (arccos α) := by
  rcases le_or_gt (-1) α with h | h
  · rw [cos_arccos h hα.le]
  · rw [arccos_of_le_neg_one h.le, cos_pi]
    exact h.le

/-- **The mass of a window under the arcsine measure.** For `a < b`,
`ω_{[a,b]}((c - r, c + r)) ≤ 2 √(r / (b - a))` for all reals `c` and `r`. -/
@[zeta5irr "lem_config_window_mass"]
theorem arcsineMeasure_Ioo_le {a b : ℝ} (hab : a < b) (c r : ℝ) :
    arcsineMeasure a b (Ioo (c - r) (c + r)) ≤ ENNReal.ofReal (2 * √(r / (b - a))) := by
  have hpi := pi_pos
  have hL : 0 < b - a := sub_pos.2 hab
  have hh : 0 < (b - a) / 2 := by linarith
  rw [arcsineMeasure_eq_volume_Ioo_zero_pi hab measurableSet_Ioo]
  set α := (c - r - (a + b) / 2) / ((b - a) / 2) with hα
  set β := (c + r - (a + b) / 2) / ((b - a) / 2) with hβ
  have hsub : Ioo 0 π ∩ (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) ⁻¹' Ioo (c - r) (c + r) ⊆
      Icc (arccos β) (arccos α) := by
    rintro θ ⟨hθ, h1, h2⟩
    have hcθ : arccos (cos θ) = θ := arccos_cos hθ.1.le hθ.2.le
    have hlo : α ≤ cos θ := by rw [hα, div_le_iff₀ hh]; linarith
    have hhi : cos θ ≤ β := by rw [hβ, le_div_iff₀ hh]; linarith
    exact ⟨hcθ ▸ arccos_le_arccos hhi, hcθ ▸ arccos_le_arccos hlo⟩
  refine (mul_le_mul' le_rfl (measure_mono hsub)).trans ?_
  rw [volume_Icc, ← ENNReal.ofReal_mul (inv_nonneg.2 hpi.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_le_iff₀ hpi]
  rcases le_or_gt (arccos α) (arccos β) with h | h
  · linarith [show 0 ≤ π * (2 * √(r / (b - a))) by positivity]
  have hβ1 : -1 < β := by
    by_contra hb
    rw [arccos_of_le_neg_one (not_lt.1 hb)] at h
    linarith [arccos_le_pi α]
  have hα1 : α < 1 := by
    by_contra ha
    rw [arccos_of_one_le (not_lt.1 ha)] at h
    linarith [arccos_nonneg β]
  have hdiff : β - α = 2 ^ 2 * (r / (b - a)) := by
    rw [hα, hβ]
    field_simp
    ring
  calc arccos α - arccos β ≤ π * √(cos (arccos β) - cos (arccos α)) :=
        sub_le_pi_mul_sqrt_cos_sub_cos (arccos_nonneg β) h.le (arccos_le_pi α)
    _ ≤ π * √(β - α) := by
        gcongr
        exacts [cos_arccos_le hβ1, le_cos_arccos hα1]
    _ = π * (2 * √(r / (b - a))) := by
        rw [hdiff, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]

/-- The mass of a window under the arcsine measure, as a real-valued mass:
`ω_{[a,b]}((c - r, c + r)) ≤ 2 √(r / (b - a))` for all reals `c` and `r`. -/
theorem measureReal_arcsineMeasure_Ioo_le {a b : ℝ} (hab : a < b) (c r : ℝ) :
    (arcsineMeasure a b).real (Ioo (c - r) (c + r)) ≤ 2 * √(r / (b - a)) := by
  have := isProbabilityMeasure_arcsineMeasure hab
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (arcsineMeasure_Ioo_le hab c r)

end Zeta5Irr
