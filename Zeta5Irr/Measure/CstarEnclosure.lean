/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Cstar
public import Zeta5Irr.Measure.EncLogSpec

/-!
# A numerical enclosure of the norm constant `C_*`

The norm constant `C_* = -2 λ + 12 α λ (1 - log α) + 3 λ² - 2 λ² log (2 λ)`, with
`α = 3/40` and `λ = 37/40`, satisfies
`2653035990340 / 10¹² < C_* < 2653035990341 / 10¹²`; numerically `C_* = 2.653035990340488…`.

Its only irrational ingredients are `log (3/40) = log (6/5) - 4 log 2` and `log (37/20)`.
Each of `log 2`, `log (6/5)` and `log (37/20)` is `log ((1 + z) / (1 - z))` for
`z = 1/3`, `1/11` and `17/57` respectively, and is enclosed between `Λ_m(z)` and
`Λ_m(z) + 2 z^{2m+1} / ((2m+1) (1 - z²))`. The resulting rational bounds are then combined
linearly.

## Main results

* `Zeta5Irr.lt_normConstant`: `2653035990340 / 10¹² < C_*`.
* `Zeta5Irr.normConstant_lt`: `C_* < 2653035990341 / 10¹²`.

## Implementation notes

* The source applies the enclosure with `m = 64`, whose error is below `2^{-144}`. The
  asserted enclosure has width `10⁻¹²`, and `m = 16` already gives errors below `10⁻¹⁵`;
  the smaller truncation keeps the rational arithmetic small. The error bound
  `2 z^{33} / (33 (1 - z²))` is evaluated directly rather than through `2^{-144}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.8: the energy and the constant.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- Rational enclosures of `log 2`, `log (6/5)` and `log (37/20)`, together with the
expression of `C_*` in terms of them. -/
private lemma normConstant_bounds :
    normConstant = -37 / 20 + 333 / 400 * (1 - (log (6 / 5) - 4 * log 2)) + 4107 / 1600 -
        1369 / 800 * log (37 / 20) ∧
      logApprox 16 (1 / 3 : ℝ) ≤ log 2 ∧
      log 2 ≤ logApprox 16 (1 / 3 : ℝ) +
        2 * (1 / 3 : ℝ) ^ (2 * 16 + 1) / ((2 * 16 + 1) * (1 - (1 / 3) ^ 2)) ∧
      logApprox 16 (1 / 11 : ℝ) ≤ log (6 / 5) ∧
      log (6 / 5) ≤ logApprox 16 (1 / 11 : ℝ) +
        2 * (1 / 11 : ℝ) ^ (2 * 16 + 1) / ((2 * 16 + 1) * (1 - (1 / 11) ^ 2)) ∧
      logApprox 16 (17 / 57 : ℝ) ≤ log (37 / 20) ∧
      log (37 / 20) ≤ logApprox 16 (17 / 57 : ℝ) +
        2 * (17 / 57 : ℝ) ^ (2 * 16 + 1) / ((2 * 16 + 1) * (1 - (17 / 57) ^ 2)) := by
  have e : log (3 / 40 : ℝ) = log (6 / 5) - 4 * log 2 := by
    rw [show (3 / 40 : ℝ) = 6 / 5 / 2 ^ 4 by norm_num, log_div (by norm_num) (by norm_num),
      log_pow]
    push_cast
    ring
  have h2 := log_div_mem_logApprox (z := 1 / 3) (by norm_num) (by norm_num) 16
  have h65 := log_div_mem_logApprox (z := 1 / 11) (by norm_num) (by norm_num) 16
  have h37 := log_div_mem_logApprox (z := 17 / 57) (by norm_num) (by norm_num) 16
  rw [show (1 + 1 / 3) / (1 - 1 / 3) = (2 : ℝ) by norm_num] at h2
  rw [show (1 + 1 / 11) / (1 - 1 / 11) = (6 / 5 : ℝ) by norm_num] at h65
  rw [show (1 + 17 / 57) / (1 - 17 / 57) = (37 / 20 : ℝ) by norm_num] at h37
  push_cast at h2 h65 h37
  exact ⟨by rw [normConstant_eq, e], h2.1, h2.2, h65.1, h65.2, h37.1, h37.2⟩

/-- The lower bound `2653035990340 / 10¹² < C_*`. -/
@[zeta5irr "lem_Cstar_enclosure"]
theorem lt_normConstant : (2653035990340 / 10 ^ 12 : ℝ) < normConstant := by
  obtain ⟨e, h2, -, -, h65, -, h37⟩ := normConstant_bounds
  simp only [logApprox, Finset.sum_range_succ, Finset.sum_range_zero] at h2 h65 h37
  norm_num at h2 h65 h37
  rw [e]
  linarith

/-- The upper bound `C_* < 2653035990341 / 10¹²`. -/
@[zeta5irr "lem_Cstar_enclosure"]
theorem normConstant_lt : normConstant < 2653035990341 / 10 ^ 12 := by
  obtain ⟨e, -, h2, h65, -, h37, -⟩ := normConstant_bounds
  simp only [logApprox, Finset.sum_range_succ, Finset.sum_range_zero] at h2 h65 h37
  norm_num at h2 h65 h37
  rw [e]
  linarith

end Zeta5Irr
