/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VDeriv
public import Zeta5Irr.Measure.VQpmNotation
public import Zeta5Irr.Measure.EncAtanSpec
public import Mathlib.Tactic.ENatToNat

/-!
# Locating the sign change of the field derivative

With `W(y) = 2 (π + arctan (1 / y) - 6 arctan (α / y))`, `α = 3/40`, and the bracket
`q₋ = 59205077 / 10¹⁰`, `q₊ = 59205079 / 10¹⁰`, one has
`W(√q₋) < 0 < W(√q₊)`.

For `y > 0` the identities `arctan (1 / y) = π/2 - arctan y` and
`arctan (α / y) = π/4 - arctan ((y - α) / (y + α))` make the multiples of `π` cancel:
`W(y) = 2 (6 arctan ((y - α) / (y + α)) - arctan y)`.
Both arctangents are increasing in `y`, so bracketing `√q` between two rationals `a ≤ √q ≤ b`
with `b - a = 10⁻¹⁰` reduces each sign to an inequality between arctangents at rational
points, each of which is enclosed by the truncated arctangent series `T_4` with its
alternating-series error bound.

## Main results

* `Zeta5Irr.fieldDeriv_eq_of_pos`: `W(y) = 2 (6 arctan ((y - α) / (y + α)) - arctan y)` for
  `y > 0`.
* `Zeta5Irr.fieldDeriv_sqrt_externalFieldMinLower_neg`: `W(√q₋) < 0`.
* `Zeta5Irr.fieldDeriv_sqrt_externalFieldMinUpper_pos`: `0 < W(√q₊)`.

## Implementation notes

* The source encloses `π`, `√q` and the three arctangents of `W(√q)` separately, using the
  Machin formula for `π`, the rational square-root enclosure `s(q)` and the half-angle
  reduction, each to accuracy `2⁻¹⁴⁴`. Here the addition formula for the arctangent removes
  `π` altogether, the arguments `√q` and `(√q - α) / (√q + α)` of the two remaining
  arctangents are already smaller than `1/10`, and `√q` is bracketed by explicit decimals;
  the four-term truncation `T_4` then suffices, with error below `10⁻¹⁰`, against margins
  above `2 · 10⁻⁸`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5 (The shape of the field).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For `y > 0` the multiples of `π` in `W` cancel:
`W(y) = 2 (6 arctan ((y - α) / (y + α)) - arctan y)`. -/
theorem fieldDeriv_eq_of_pos {y : ℝ} (hy : 0 < y) :
    fieldDeriv y =
      2 * (6 * arctan ((y - innerRatio) / (y + innerRatio)) - arctan y) := by
  set a : ℝ := (innerRatio : ℝ)
  have ha : 0 < a := by simp [a, innerRatio]
  have h1 : arctan (1 / y) = π / 2 - arctan y := by
    rw [one_div, arctan_inv_of_pos hy]
  have h2 : arctan (a / y) = π / 4 - arctan ((y - a) / (y + a)) := by
    have hlt : (a - y) / (a + y) * 1 < 1 := by
      rw [mul_one, div_lt_one (by positivity)]
      linarith
    have := arctan_add hlt
    rw [arctan_one] at this
    have e : ((a - y) / (a + y) + 1) / (1 - (a - y) / (a + y) * 1) = a / y := by
      have := hy.ne'
      field_simp
      rw [show a - y + (a + y) = 2 * a by ring, show a + y - (a - y) = 2 * y by ring]
      field_simp
    have e' : (a - y) / (a + y) = -((y - a) / (y + a)) := by
      rw [← neg_div, neg_sub, add_comm]
    rw [e, e', arctan_neg] at this
    linarith
  rw [fieldDeriv, h1, h2]
  ring

/-- The inner ratio `α = 3/40`, as a real number. -/
private lemma innerRatio_cast : ((innerRatio : ℚ) : ℝ) = 3 / 40 := by
  simp [innerRatio]

/-- The map `y ↦ (y - α) / (y + α)` is monotone on `(0, ∞)`. -/
private lemma div_sub_add_le {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    (y - 3 / 40) / (y + 3 / 40) ≤ (z - 3 / 40) / (z + 3 / 40) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `W(√q₋) < 0`. -/
@[zeta5irr "lem_V_min_locate"]
theorem fieldDeriv_sqrt_externalFieldMinLower_neg :
    fieldDeriv √(externalFieldMinLower : ℝ) < 0 := by
  set y := √(externalFieldMinLower : ℝ)
  have hay : (769448354 / 10 ^ 10 : ℝ) ≤ y :=
    Real.le_sqrt_of_sq_le (by norm_num [externalFieldMinLower])
  have hyb : y ≤ (769448355 / 10 ^ 10 : ℝ) :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num [externalFieldMinLower])
  have hy : 0 < y := lt_of_lt_of_le (by norm_num) hay
  rw [fieldDeriv_eq_of_pos hy, innerRatio_cast]
  have hu := arctan_strictMono.monotone (div_sub_add_le hy hyb)
  have hv := arctan_strictMono.monotone hay
  have hbu := arctan_le_atanApprox_add
    (z := ((769448355 / 10 ^ 10 : ℝ) - 3 / 40) / (769448355 / 10 ^ 10 + 3 / 40))
    (by norm_num) (by norm_num) 4
  have hba := atanApprox_sub_le_arctan (z := (769448354 / 10 ^ 10 : ℝ)) (by norm_num)
    (by norm_num) 4
  push_cast at hbu hba
  have key : 6 * (atanApprox 4
        (((769448355 / 10 ^ 10 : ℝ) - 3 / 40) / (769448355 / 10 ^ 10 + 3 / 40)) +
        (((769448355 / 10 ^ 10 : ℝ) - 3 / 40) / (769448355 / 10 ^ 10 + 3 / 40)) ^ 9 / 9) <
      atanApprox 4 (769448354 / 10 ^ 10 : ℝ) - (769448354 / 10 ^ 10 : ℝ) ^ 9 / 9 := by
    norm_num [atanApprox, Finset.sum_range_succ]
  linarith

/-- `0 < W(√q₊)`. -/
@[zeta5irr "lem_V_min_locate"]
theorem fieldDeriv_sqrt_externalFieldMinUpper_pos :
    0 < fieldDeriv √(externalFieldMinUpper : ℝ) := by
  set y := √(externalFieldMinUpper : ℝ)
  have hay : (769448367 / 10 ^ 10 : ℝ) ≤ y :=
    Real.le_sqrt_of_sq_le (by norm_num [externalFieldMinUpper])
  have hyb : y ≤ (769448368 / 10 ^ 10 : ℝ) :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num [externalFieldMinUpper])
  have hy : 0 < y := lt_of_lt_of_le (by norm_num) hay
  rw [fieldDeriv_eq_of_pos hy, innerRatio_cast]
  have hu := arctan_strictMono.monotone (div_sub_add_le (by norm_num) hay)
  have hv := arctan_strictMono.monotone hyb
  have hau := atanApprox_sub_le_arctan
    (z := ((769448367 / 10 ^ 10 : ℝ) - 3 / 40) / (769448367 / 10 ^ 10 + 3 / 40))
    (by norm_num) (by norm_num) 4
  have hbb := arctan_le_atanApprox_add (z := (769448368 / 10 ^ 10 : ℝ)) (by norm_num)
    (by norm_num) 4
  push_cast at hau hbb
  have key : atanApprox 4 (769448368 / 10 ^ 10 : ℝ) + (769448368 / 10 ^ 10 : ℝ) ^ 9 / 9 <
      6 * (atanApprox 4
        (((769448367 / 10 ^ 10 : ℝ) - 3 / 40) / (769448367 / 10 ^ 10 + 3 / 40)) -
        (((769448367 / 10 ^ 10 : ℝ) - 3 / 40) / (769448367 / 10 ^ 10 + 3 / 40)) ^ 9 / 9) := by
    norm_num [atanApprox, Finset.sum_range_succ]
  linarith

end Zeta5Irr
