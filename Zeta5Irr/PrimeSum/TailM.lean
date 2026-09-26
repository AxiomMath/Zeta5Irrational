/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.TailIbp

/-!
# The tail integral at a multiple of `40`

For every integer `M ≥ 40` divisible by `40`,
`∫_M^∞ R(x) x⁻³ dx ≥ -λ/M + (2923/240 - 1/4)/M² - 32/M³`, where `R` is the inner limiting
function and `λ = 37/40`.

At such `M` both `M` and `α M = 3M/40` are integers, so the first and second periodic
antiderivatives vanish at `M`, and the integration-by-parts formula for the tail integral
reduces to `-λ/M + 2923/(240 M²) + 6 ∫_M^∞ 𝒫₂(x) x⁻⁴ dx + ∫_M^∞ 𝓔(x) x⁻³ dx`. The bounds
`|𝒫₂| ≤ 16` and `𝓔 ≥ -1/2`, with `∫_M^∞ x⁻⁴ dx = 1/(3M³)` and `∫_M^∞ x⁻³ dx = 1/(2M²)`,
bound the last two terms below by `-32/M³` and `-(1/4)/M²`.

## Main results

* `Zeta5Irr.firstPeriodicAntideriv_eq_zero_of_forty_dvd`,
  `Zeta5Irr.secondPeriodicAntideriv_eq_zero_of_forty_dvd`: `𝒫(M) = 𝒫₂(M) = 0` when `40 ∣ M`.
* `Zeta5Irr.integral_Ioi_innerLimitingR_div_pow_three_ge_of_forty_dvd`: the lower bound for
  the tail integral at a multiple of `40`.

## Implementation notes

* The source assumes `M ≥ 40`; the proof only uses `M > 0`, which for a multiple of `40` is
  the same condition.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- If `40 ∣ M` then `α M = 3M/40` is an integer. -/
theorem innerRatio_mul_eq_intCast_of_forty_dvd {M : ℤ} (hM : 40 ∣ M) :
    (innerRatio : ℝ) * M = ((3 * (M / 40) : ℤ) : ℝ) := by
  obtain ⟨k, rfl⟩ := hM
  rw [Int.mul_ediv_cancel_left _ (by norm_num)]
  simp only [innerRatio]
  push_cast
  ring

/-- `𝒫(M) = 0` when `M` is an integer divisible by `40`. -/
theorem firstPeriodicAntideriv_eq_zero_of_forty_dvd {M : ℤ} (hM : 40 ∣ M) :
    firstPeriodicAntideriv M = 0 := by
  rw [firstPeriodicAntideriv, innerRatio_mul_eq_intCast_of_forty_dvd hM, Int.fract_intCast,
    Int.fract_intCast]
  simp

/-- `𝒫₂(M) = 0` when `M` is an integer divisible by `40`. -/
theorem secondPeriodicAntideriv_eq_zero_of_forty_dvd {M : ℤ} (hM : 40 ∣ M) :
    secondPeriodicAntideriv M = 0 := by
  rw [secondPeriodicAntideriv, innerRatio_mul_eq_intCast_of_forty_dvd hM, Int.fract_intCast,
    Int.fract_intCast]
  simp

/-- **The tail integral at a multiple of `40`.** For every integer `M ≥ 40` divisible by `40`,
`∫_M^∞ R(x)/x³ dx ≥ -λ/M + (2923/240 - 1/4)/M² - 32/M³`. -/
@[zeta5irr "lem_tail_M"]
theorem integral_Ioi_innerLimitingR_div_pow_three_ge_of_forty_dvd {M : ℤ} (hM : 40 ∣ M)
    (hM40 : 40 ≤ M) :
    -((orderRatio : ℝ) / M) + (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 - 32 / (M : ℝ) ^ 3 ≤
      ∫ x in Ioi (M : ℝ), innerLimitingR x / x ^ 3 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show (0 : ℤ) < M by omega)
  rw [integral_Ioi_innerLimitingR_div_pow_three_eq hM0,
    firstPeriodicAntideriv_eq_zero_of_forty_dvd hM,
    secondPeriodicAntideriv_eq_zero_of_forty_dvd hM]
  have hP₂ : IntegrableOn (fun x => secondPeriodicAntideriv x / x ^ 4) (Ioi (M : ℝ)) :=
    integrableOn_Ioi_div_pow continuous_secondPeriodicAntideriv.aestronglyMeasurable
      abs_secondPeriodicAntideriv_le (by norm_num) hM0
  have hR : IntegrableOn (fun x => innerLimitingR x / x ^ 3) (Ioi (M : ℝ)) :=
    (integrableOn_innerLimitingR_div_pow_three_Ici hM0).mono_set Ioi_subset_Ici_self
  -- `𝓔(x)/x³ = R(x)/x³ - Φ(x)/x²` is integrable as a difference of integrable functions
  have hE : IntegrableOn (fun x => innerSplitError x / x ^ 3) (Ioi (M : ℝ)) := by
    have hΦ : IntegrableOn (fun x => sawtoothSlope x / x ^ 2) (Ioi (M : ℝ)) :=
      integrableOn_Ioi_div_pow measurable_sawtoothSlope.aestronglyMeasurable
        abs_sawtoothSlope_le_eighteen le_rfl hM0
    refine (hR.sub hΦ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : x ≠ 0 := (hM0.trans hx).ne'
    simp only [Pi.sub_apply, innerLimitingR_eq]
    field_simp
    ring
  have hI4 : -16 * (1 / (3 * (M : ℝ) ^ 3)) ≤
      ∫ x in Ioi (M : ℝ), secondPeriodicAntideriv x / x ^ 4 := by
    convert le_setIntegral_Ioi_div_pow hM0 (k := 4) (by norm_num) hP₂
      fun x _ => neg_le_of_abs_le (abs_secondPeriodicAntideriv_le x) using 1
    norm_num
    ring
  have hI3 : -(1 / 2) * (1 / (2 * (M : ℝ) ^ 2)) ≤
      ∫ x in Ioi (M : ℝ), innerSplitError x / x ^ 3 := by
    convert le_setIntegral_Ioi_div_pow hM0 (k := 3) (by norm_num) hE
      fun x _ => neg_half_le_innerSplitError x using 1
    norm_num
    ring
  have e1 : (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 =
      2923 / (240 * (M : ℝ) ^ 2) + -(1 / 2) * (1 / (2 * (M : ℝ) ^ 2)) := by
    field_simp; ring
  have e2 : 32 / (M : ℝ) ^ 3 = -(6 * (-16 * (1 / (3 * (M : ℝ) ^ 3)))) := by
    field_simp; ring
  simp only [zero_div, sub_zero, mul_zero]
  rw [e1, e2]
  linarith

end Zeta5Irr
