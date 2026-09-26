/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.EncAtan
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Error bound for the truncated arctangent series

For `|z| < 1` the arctangent is the sum of its Taylor series
`arctan z = ∑_{k ≥ 0} (-1)^k z^{2k+1} / (2k+1)`. For `0 ≤ z < 1` the terms
`u_k = z^{2k+1} / (2k+1)` are nonnegative and nonincreasing, so the alternating series error
bound gives `|arctan z - T_m(z)| ≤ u_m`, where `T_m` is the truncation after `m` terms. By
oddness of both sides the bound `|arctan z - T_m(z)| ≤ |z|^{2m+1} / (2m+1)` holds for every
`|z| < 1`.

## Main results

* `Zeta5Irr.abs_arctan_sub_atanApprox_le_of_nonneg`: for `0 ≤ z < 1` and every `m`,
  `|arctan z - T_m(z)| ≤ z^{2m+1} / (2m+1)`.
* `Zeta5Irr.atanApprox_sub_le_arctan`, `Zeta5Irr.arctan_le_atanApprox_add`: the two one-sided
  forms of this bound.
* `Zeta5Irr.abs_arctan_sub_atanApprox_le`: for `|z| < 1` and every `m`,
  `|arctan z - T_m(z)| ≤ |z|^{2m+1} / (2m+1)`.

## Implementation notes

* The source states the bound for `0 ≤ z ≤ 1/2` and `m ≥ 1`. It is proved here for every real
  `z` with `|z| < 1` (with `|z|^{2m+1}` in place of `z^{2m+1}`) and every `m`, which contains
  the source statement.
* The source proves the alternating tail bound by grouping terms in pairs; here it is
  `alternating_series_error_bound`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `0 ≤ z < 1`, `|arctan z - T_m(z)| ≤ z^{2m+1} / (2m+1)`. -/
theorem abs_arctan_sub_atanApprox_le_of_nonneg {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    |Real.arctan z - atanApprox m z| ≤ z ^ (2 * m + 1) / (2 * m + 1) := by
  set u : ℕ → ℝ := fun k => z ^ (2 * k + 1) / (2 * k + 1) with hu
  have hsum : HasSum (fun k => (-1) ^ k * u k) (Real.arctan z) := by
    have := Real.hasSum_arctan (x := z) (by rw [Real.norm_eq_abs, abs_of_nonneg h₀]; exact h₁)
    convert this using 2 with k
    simp [hu, mul_div_assoc]
  have hanti : Antitone u := by
    refine antitone_nat_of_succ_le fun k => ?_
    simp only [hu]
    push_cast
    have h1 : z ^ (2 * (k + 1) + 1) ≤ z ^ (2 * k + 1) :=
      pow_le_pow_of_le_one h₀ h₁.le (by omega)
    have h2 : (2 * k + 1 : ℝ) ≤ 2 * (k + 1) + 1 := by linarith
    exact div_le_div₀ (pow_nonneg h₀ _) h1 (by positivity) h2
  have hsu : Summable u := by
    refine (summable_abs_iff.mpr hsum.summable).congr fun k => ?_
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]
  have := alternating_series_error_bound u hanti hsu m
  rw [hsum.tsum_eq] at this
  convert this using 3
  simp [atanApprox, hu, mul_div_assoc]

/-- For `0 ≤ z < 1`, `T_m(z) - z^{2m+1} / (2m+1) ≤ arctan z`. -/
theorem atanApprox_sub_le_arctan {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    atanApprox m z - z ^ (2 * m + 1) / (2 * m + 1) ≤ Real.arctan z := by
  linarith [(abs_le.1 (abs_arctan_sub_atanApprox_le_of_nonneg h₀ h₁ m)).1]

/-- For `0 ≤ z < 1`, `arctan z ≤ T_m(z) + z^{2m+1} / (2m+1)`. -/
theorem arctan_le_atanApprox_add {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    Real.arctan z ≤ atanApprox m z + z ^ (2 * m + 1) / (2 * m + 1) := by
  linarith [(abs_le.1 (abs_arctan_sub_atanApprox_le_of_nonneg h₀ h₁ m)).2]

/-- For `|z| < 1` and every `m`, `|arctan z - T_m(z)| ≤ |z|^{2m+1} / (2m+1)`. -/
@[zeta5irr "lem_enc_atan"]
theorem abs_arctan_sub_atanApprox_le {z : ℝ} (hz : |z| < 1) (m : ℕ) :
    |Real.arctan z - atanApprox m z| ≤ |z| ^ (2 * m + 1) / (2 * m + 1) := by
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h] at hz ⊢
    exact abs_arctan_sub_atanApprox_le_of_nonneg h hz m
  · rw [abs_of_nonpos h] at hz ⊢
    have := abs_arctan_sub_atanApprox_le_of_nonneg (neg_nonneg.mpr h) hz m
    rwa [Real.arctan_neg, atanApprox_neg, ← neg_add', abs_neg, ← sub_eq_add_neg] at this

end Zeta5Irr
