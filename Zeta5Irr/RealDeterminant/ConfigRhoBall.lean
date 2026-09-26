/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Rho
public import Zeta5Irr.Measure.RhoLength
public import Zeta5Irr.Measure.RhoMass
public import Zeta5Irr.RealDeterminant.ConfigWindowMass

/-!
# A bound on the `ρ`-mass of a disc

For every `z ∈ ℂ` and every `r > 0`, the real points of the open disc of radius `r` about `z`
carry `ρ`-mass at most `28 √r`. The set `{u ∈ ℝ : |z - u| < r}` lies in the window
`(Re z - r, Re z + r)`; each arcsine measure `ω_{[aⱼ, bⱼ]}` gives this window mass at most
`2 √(r / (bⱼ - aⱼ)) ≤ 30 √r`, since `bⱼ - aⱼ > 1 / 225`; summing with the weights `cⱼ`, whose
total is `λ = 37 / 40`, gives `ρ ≤ 30 · 37 / 40 · √r = 27.75 √r ≤ 28 √r`.

## Main results

* `Zeta5Irr.rho_ball_le`: `ρ({u ∈ ℝ : |z - u| < r}) ≤ 28 √r`.

## Implementation notes

* The measure `ρ` takes values in `ℝ≥0∞`, so the bound reads `≤ ENNReal.ofReal (28 * √r)`.
* The hypothesis `r > 0` is not needed: for `r ≤ 0` the set is empty.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- **The `ρ`-mass of a disc.** For every `z ∈ ℂ` and every real `r`, the real points of the
open disc of radius `r` about `z` have `ρ`-mass at most `28 √r`. -/
@[zeta5irr "lem_config_rho_ball"]
theorem rho_ball_le (z : ℂ) (r : ℝ) :
    rho {u : ℝ | ‖z - u‖ < r} ≤ ENNReal.ofReal (28 * √r) := by
  have hsub : {u : ℝ | ‖z - u‖ < r} ⊆ Ioo (z.re - r) (z.re + r) := by
    intro u hu
    have h := (Complex.abs_re_le_norm (z - u)).trans_lt hu
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact ⟨by linarith [(abs_lt.1 h).2], by linarith [(abs_lt.1 h).1]⟩
  refine (measure_mono hsub).trans ?_
  rw [rho_apply]
  have hc : ∀ j, (0 : ℝ) ≤ rhoC j := fun j ↦ by exact_mod_cast rhoC_nonneg j
  calc ∑ j : Fin 16, ENNReal.ofReal (rhoC j) *
        arcsineMeasure (rhoA j) (rhoB j) (Ioo (z.re - r) (z.re + r))
      ≤ ∑ j : Fin 16, ENNReal.ofReal (rhoC j) * ENNReal.ofReal (30 * √r) := by
        gcongr with j
        refine (arcsineMeasure_Ioo_le (rhoA_lt_rhoB_real j) _ _).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hL : (1 : ℝ) / 225 < (rhoB j : ℝ) - rhoA j := by
          have h := (Rat.cast_lt (K := ℝ)).2 (rho_length j)
          push_cast at h
          exact h
        have hL0 : (0 : ℝ) < (rhoB j : ℝ) - rhoA j := lt_trans (by norm_num) hL
        rcases le_or_gt r 0 with hr | hr
        · rw [Real.sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg hr hL0.le)]
          rw [mul_zero]; positivity
        have : √(r / (rhoB j - rhoA j)) ≤ √(225 * r) := by
          gcongr
          rw [div_le_iff₀ hL0]
          nlinarith
        rw [Real.sqrt_mul (by norm_num), show √(225 : ℝ) = 15 by
          rw [show (225 : ℝ) = 15 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
        linarith
    _ = ENNReal.ofReal ((∑ j : Fin 16, (rhoC j : ℝ)) * (30 * √r)) := by
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ ↦ hc j),
          ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hc j, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (28 * √r) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Rat.cast_sum, sum_rhoC, orderRatio]
        have := Real.sqrt_nonneg r
        push_cast
        nlinarith

end Zeta5Irr
