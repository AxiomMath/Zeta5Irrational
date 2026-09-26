/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotParam

/-!
# The distribution function of the arcsine measure

For reals `a < b` and `0 ≤ y ≤ b - a`, the arcsine measure `ω_{[a,b]}` gives the interval
`[a, a + y]` the mass `(2/π) arcsin √(y / (b - a))`.

Write `L = b - a`. Along the parametrisation `θ ↦ (a + b)/2 + (L/2) cos θ` of `(a, b)` by the
half-circle `(0, π)`, the arcsine measure is `π⁻¹` times Lebesgue measure. The point
`(a + b)/2 + (L/2) cos θ` lies in `[a, a + y]` exactly when `cos θ ≤ c` with `c = 2y/L - 1`,
that is, when `arccos c ≤ θ`. The mass is therefore `(π - arccos c)/π = arccos (1 - 2y/L)/π`,
and the half-angle identity `arccos (1 - 2t) = 2 arcsin √t` finishes the computation.

## Main results

* `Zeta5Irr.arccos_one_sub_two_mul`: `arccos (1 - 2t) = 2 arcsin √t` for every real `t`.
* `Zeta5Irr.arcsineMeasure_Icc_left`: `ω_{[a,b]}([a, a + y]) = (2/π) arcsin √(y / (b - a))`.
* `Zeta5Irr.measureReal_arcsineMeasure_Icc_left`: the same identity for the real-valued mass.

## Implementation notes

* The blueprint substitutes `u = a + L sin² θ` in the density integral on `[0, arcsin √(y/L)]`.
  Here the mass is read off instead from the parametrisation of `ω_{[a,b]}` by the half-circle
  (the change of variables `θ ↦ (a + b)/2 + (L/2) cos θ` of §9.2), which reduces it to the
  length of an interval of angles; the two routes are related by `θ ↦ π - 2θ`.
* The hypothesis `0 ≤ y ≤ b - a` of the source is dropped: with `√` truncated at `0` and
  `arcsin` at `π/2`, both sides are `0` for `y < 0` and `1` for `y > b - a`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real
open scoped ENNReal

/-- The half-angle identity `arccos (1 - 2t) = 2 arcsin √t`. It holds for every real `t`: for
`t ≤ 0` both sides vanish, and for `1 ≤ t` both sides equal `π`. -/
lemma arccos_one_sub_two_mul (t : ℝ) : arccos (1 - 2 * t) = 2 * arcsin √t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [sqrt_eq_zero'.2 ht, arcsin_zero, mul_zero, arccos_eq_zero.2 (by linarith)]
  rcases le_or_gt 1 t with ht1 | ht1
  · rw [arcsin_of_one_le (one_le_sqrt.2 ht1), arccos_of_le_neg_one (by linarith)]
    ring
  have hs0 : 0 ≤ √t := sqrt_nonneg t
  have hs1 : √t ≤ 1 := sqrt_le_one.2 ht1.le
  have hmem : 2 * arcsin √t ∈ Icc 0 π :=
    ⟨by linarith [arcsin_nonneg.2 hs0], by linarith [arcsin_le_pi_div_two √t]⟩
  rw [← arccos_cos hmem.1 hmem.2, cos_two_mul_eq_one_sub, sin_arcsin (by linarith) hs1,
    sq_sqrt ht.le]

/-- On the open half-circle `(0, π)`, `arccos c ≤ θ` if and only if `cos θ ≤ c`, for every real
`c`. -/
lemma arccos_le_iff_cos_le {c θ : ℝ} (hθ : θ ∈ Ioo 0 π) : arccos c ≤ θ ↔ cos θ ≤ c := by
  refine ⟨fun h ↦ ?_, fun h ↦ (arccos_le_arccos h).trans_eq (arccos_cos hθ.1.le hθ.2.le)⟩
  rcases le_or_gt 1 c with hc | hc
  · exact (cos_le_one θ).trans hc
  rcases le_or_gt c (-1) with hc' | hc'
  · rw [arccos_of_le_neg_one hc'] at h
    linarith [hθ.2]
  by_contra! hlt
  have := arccos_lt_arccos hc'.le hlt (cos_le_one θ)
  rw [arccos_cos hθ.1.le hθ.2.le] at this
  linarith

/-- **The distribution function of the arcsine measure.** For `a < b`,
`ω_{[a,b]}([a, a + y]) = (2/π) arcsin √(y / (b - a))`. This holds for every real `y`: for `y < 0`
both sides vanish, and for `b - a ≤ y` both sides equal `1`. -/
@[zeta5irr "lem_config_arcsine_cdf"]
theorem arcsineMeasure_Icc_left {a b : ℝ} (hab : a < b) (y : ℝ) :
    arcsineMeasure a b (Icc a (a + y)) = ENNReal.ofReal (2 / π * arcsin √(y / (b - a))) := by
  have hL : 0 < b - a := sub_pos.2 hab
  set c : ℝ := 2 * (y / (b - a)) - 1 with hc
  rw [arcsineMeasure_eq_volume_Ioo_zero_pi hab measurableSet_Icc]
  have hset : Ioo 0 π ∩ (fun θ ↦ (a + b) / 2 + (b - a) / 2 * cos θ) ⁻¹' Icc a (a + y) =
      Ioo 0 π ∩ Ici (arccos c) := by
    ext θ
    simp only [mem_inter_iff, mem_Ioo, mem_preimage, mem_Icc, mem_Ici]
    refine and_congr_right fun hθ ↦ ?_
    rw [arccos_le_iff_cos_le hθ, hc, le_sub_iff_add_le, mul_div_assoc', le_div_iff₀ hL]
    exact ⟨fun ⟨_, _⟩ ↦ by nlinarith, fun h ↦ ⟨by nlinarith [neg_one_le_cos θ],
      by nlinarith [neg_one_le_cos θ]⟩⟩
  have hvol : volume (Ioo 0 π ∩ Ici (arccos c)) = ENNReal.ofReal (π - arccos c) := by
    refine le_antisymm ?_ ?_
    · calc volume (Ioo 0 π ∩ Ici (arccos c)) ≤ volume (Icc (arccos c) π) :=
            measure_mono fun θ hθ ↦ ⟨hθ.2, hθ.1.2.le⟩
        _ = _ := volume_Icc
    · calc ENNReal.ofReal (π - arccos c) = volume (Ioo (arccos c) π) := volume_Ioo.symm
        _ ≤ volume (Ioo 0 π ∩ Ici (arccos c)) := measure_mono fun θ hθ ↦
            ⟨⟨(arccos_nonneg c).trans_lt hθ.1, hθ.2⟩, hθ.1.le⟩
  rw [hset, hvol, ← ENNReal.ofReal_mul (inv_nonneg.2 pi_pos.le), ← arccos_neg, hc,
    show -(2 * (y / (b - a)) - 1) = 1 - 2 * (y / (b - a)) by ring, arccos_one_sub_two_mul]
  congr 1
  ring

/-- The distribution function of the arcsine measure, as a real-valued mass:
`ω_{[a,b]}([a, a + y]) = (2/π) arcsin √(y / (b - a))` for every real `y`. -/
theorem measureReal_arcsineMeasure_Icc_left {a b : ℝ} (hab : a < b) (y : ℝ) :
    (arcsineMeasure a b).real (Icc a (a + y)) = 2 / π * arcsin √(y / (b - a)) := by
  rw [measureReal_def, arcsineMeasure_Icc_left hab, ENNReal.toReal_ofReal]
  exact mul_nonneg (div_nonneg zero_le_two pi_pos.le) (arcsin_nonneg.2 (sqrt_nonneg _))

end Zeta5Irr
