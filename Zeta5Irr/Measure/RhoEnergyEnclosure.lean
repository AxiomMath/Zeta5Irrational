/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoEnergyFormula
public import Zeta5Irr.Measure.EncLogSpec

/-!
# A numerical enclosure of the energy `I(ρ)`

The logarithmic energy of the rational arcsine measure `ρ = ∑ⱼ cⱼ ω_{[aⱼ, bⱼ]}` satisfies
`-2126593445148 / 10¹² < I(ρ) < -2126593445147 / 10¹²`; numerically
`I(ρ) = -2.126593445147050…`.

By the energy formula, `I(ρ) = ∑ⱼ (Sⱼ² - S_{j-1}²) log ((bⱼ - aⱼ)/4)`, where the coefficients
`Sⱼ² - S_{j-1}²` are nonnegative rationals. For each `j` we write
`(bⱼ - aⱼ)/4 = 2^{-kⱼ} yⱼ` with `kⱼ ∈ ℕ` and `1 ≤ yⱼ < 2`, so that
`log ((bⱼ - aⱼ)/4) = log yⱼ - kⱼ log 2`. With `z = (y - 1)/(y + 1) ∈ [0, 1/3]` one has
`y = (1 + z)/(1 - z)`, hence `Λ_m(z) ≤ log y ≤ Λ_m(z) + 2 z^{2m+1} / ((2m+1)(1 - z²))`;
`log 2` is the case `y = 2`, `z = 1/3`. Substituting these rational bounds term by term gives
rational lower and upper bounds for `I(ρ)`, which are compared with the asserted endpoints by
exact rational arithmetic.

## Main results

* `Zeta5Irr.lt_logEnergy_rho`: `-2126593445148 / 10¹² < I(ρ)`.
* `Zeta5Irr.logEnergy_rho_lt`: `I(ρ) < -2126593445147 / 10¹²`.

## Implementation notes

* The source applies the enclosure with `m = 64`, whose error is below `2^{-144}`. The
  asserted enclosure has width `10⁻¹²`, and the upper endpoint lies only about `5 · 10⁻¹⁴`
  above `I(ρ)`; `m = 16` already bounds every logarithm to within `2 · 10⁻¹⁷`, which is ample.
  The error term `2 z^{33} / (33 (1 - z²))` is kept exactly in the rational bound rather than
  estimated by a power of `2`.
* The exponents `kⱼ` are recorded in a table; the conditions `1 ≤ yⱼ` and the final
  comparisons of rationals are checked by evaluation in `ℚ`. The condition `yⱼ < 2` is not
  needed for correctness, only for the accuracy of the bounds.
* `ρ` is a measure on `ℝ`; its energy is that of its pushforward to `ℂ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.8 (The energy and the constant).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The exponents `kⱼ` with `1 ≤ 2^{kⱼ} (bⱼ - aⱼ)/4 < 2`. -/
private def rhoLogExp : Fin 16 → ℕ := ![10, 9, 8, 7, 6, 6, 5, 5, 4, 4, 4, 3, 3, 3, 3, 3]

/-- The mantissa `yⱼ = 2^{kⱼ} (bⱼ - aⱼ)/4 ∈ [1, 2)`. -/
private def rhoLogRatio (j : Fin 16) : ℚ := (rhoB j - rhoA j) / 4 * 2 ^ rhoLogExp j

/-- The argument `z = (y - 1)/(y + 1)`, for which `(1 + z)/(1 - z) = y`. -/
private def logArg (y : ℚ) : ℚ := (y - 1) / (y + 1)

/-- The error bound `2 z^{2m+1} / ((2m+1)(1 - z²))` of the enclosure `Λ_m`. -/
private def logErr (m : ℕ) (z : ℚ) : ℚ := 2 * z ^ (2 * m + 1) / ((2 * m + 1) * (1 - z ^ 2))

/-- For a rational `y ≥ 1`, with `z = (y - 1)/(y + 1)`,
`Λ_m(z) ≤ log y ≤ Λ_m(z) + 2 z^{2m+1} / ((2m+1)(1 - z²))`. -/
private lemma log_ratCast_mem {y : ℚ} (hy : 1 ≤ y) (m : ℕ) :
    (logApprox m (logArg y) : ℝ) ≤ log y ∧
      log y ≤ ((logApprox m (logArg y) + logErr m (logArg y) : ℚ) : ℝ) := by
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hz : ((logArg y : ℚ) : ℝ) = ((y : ℝ) - 1) / (y + 1) := by
    simp [logArg]
  have h0 : (0 : ℝ) ≤ (logArg y : ℚ) := by
    rw [hz]
    apply div_nonneg <;> linarith
  have h1 : ((logArg y : ℚ) : ℝ) < 1 := by
    rw [hz, div_lt_one (by linarith)]
    linarith
  have he : (1 + ((logArg y : ℚ) : ℝ)) / (1 - (logArg y : ℚ)) = y := by
    rw [hz]
    field_simp
    ring
  have h := log_div_mem_logApprox h0 h1 m
  rw [he] at h
  push_cast [logErr]
  exact h

/-- The rational upper bound for `I(ρ)`: each `log yⱼ` by its upper enclosure and `log 2` by
its lower enclosure. -/
private def rhoEnergyUpper : ℚ :=
  ∑ j : Fin 16, (rhoPartial (j + 1) ^ 2 - rhoPartial j ^ 2) *
    (logApprox 16 (logArg (rhoLogRatio j)) + logErr 16 (logArg (rhoLogRatio j)) -
      rhoLogExp j * logApprox 16 (logArg 2))

/-- The rational lower bound for `I(ρ)`: each `log yⱼ` by its lower enclosure and `log 2` by
its upper enclosure. -/
private def rhoEnergyLower : ℚ :=
  ∑ j : Fin 16, (rhoPartial (j + 1) ^ 2 - rhoPartial j ^ 2) *
    (logApprox 16 (logArg (rhoLogRatio j)) -
      rhoLogExp j * (logApprox 16 (logArg 2) + logErr 16 (logArg 2)))

private lemma one_le_rhoLogRatio : ∀ j, 1 ≤ rhoLogRatio j := by decide +kernel

private lemma rhoEnergyUpper_lt : rhoEnergyUpper < -2126593445147 / 10 ^ 12 := by
  decide +kernel

private lemma lt_rhoEnergyLower : -2126593445148 / 10 ^ 12 < rhoEnergyLower := by
  decide +kernel

/-- `log ((bⱼ - aⱼ)/4) = log yⱼ - kⱼ log 2`. -/
private lemma log_rhoLength (j : Fin 16) :
    log (((rhoB j : ℝ) - rhoA j) / 4) = log (rhoLogRatio j : ℝ) - rhoLogExp j * log 2 := by
  have := rhoA_lt_rhoB_real j
  have hpos : (0 : ℝ) < ((rhoB j : ℝ) - rhoA j) / 4 := by linarith
  rw [rhoLogRatio]
  push_cast
  rw [log_mul hpos.ne' (by positivity), log_pow]
  ring

/-- The coefficients `Sⱼ² - S_{j-1}²` of the energy formula are nonnegative. -/
private lemma rhoPartial_sq_sub_sq_nonneg (j : Fin 16) :
    (0 : ℝ) ≤ (rhoPartial (j + 1) : ℝ) ^ 2 - (rhoPartial j : ℝ) ^ 2 := by
  have h1 : rhoPartial j ≤ rhoPartial (j + 1) := rhoPartial_mono (Nat.le_succ _)
  have h0 := rhoPartial_nonneg j
  have : (0 : ℚ) ≤ rhoPartial (j + 1) ^ 2 - rhoPartial j ^ 2 := by nlinarith
  exact_mod_cast this

/-- **Upper enclosure of the energy of `ρ`.** `I(ρ) < -2126593445147 / 10¹²`. -/
@[zeta5irr "lem_rho_energy_enclosure"]
theorem logEnergy_rho_lt :
    logEnergy (rho.map ((↑) : ℝ → ℂ)) < -2126593445147 / 10 ^ 12 := by
  have h2 := log_ratCast_mem (y := 2) (by norm_num) 16
  push_cast at h2
  calc logEnergy (rho.map ((↑) : ℝ → ℂ)) ≤ (rhoEnergyUpper : ℝ) := by
        rw [logEnergy_rho, rhoEnergyUpper]
        push_cast
        refine Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left ?_ (rhoPartial_sq_sub_sq_nonneg j)
        have h := log_ratCast_mem (one_le_rhoLogRatio j) 16
        push_cast at h
        rw [log_rhoLength]
        have hk : (0 : ℝ) ≤ rhoLogExp j := Nat.cast_nonneg _
        nlinarith [h.2, h2.1]
    _ < -2126593445147 / 10 ^ 12 := by exact_mod_cast rhoEnergyUpper_lt

/-- **Lower enclosure of the energy of `ρ`.** `-2126593445148 / 10¹² < I(ρ)`. -/
@[zeta5irr "lem_rho_energy_enclosure"]
theorem lt_logEnergy_rho :
    -2126593445148 / 10 ^ 12 < logEnergy (rho.map ((↑) : ℝ → ℂ)) := by
  have h2 := log_ratCast_mem (y := 2) (by norm_num) 16
  push_cast at h2
  calc (-2126593445148 / 10 ^ 12 : ℝ) < (rhoEnergyLower : ℝ) := by
        exact_mod_cast lt_rhoEnergyLower
    _ ≤ logEnergy (rho.map ((↑) : ℝ → ℂ)) := by
        rw [logEnergy_rho, rhoEnergyLower]
        push_cast
        refine Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left ?_ (rhoPartial_sq_sub_sq_nonneg j)
        have h := log_ratCast_mem (one_le_rhoLogRatio j) 16
        push_cast at h
        rw [log_rhoLength]
        have hk : (0 : ℝ) ≤ rhoLogExp j := Nat.cast_nonneg _
        nlinarith [h.1, h2.2]

end Zeta5Irr
