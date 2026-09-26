/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.WeightClosed
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An exponential upper bound for the weight

For `y > 0` the weight satisfies `w(y) ≤ 8192 (1 + y)⁵ e^{-2πy}`.

Put `q = e^{-2πy}` and `u = 2πy > 0`. In the closed form of `w(y)` the factor
`1 + 11 q + 11 q² + q³` is at most `24`, and `e^u ≥ 1 + u` gives `1 - q ≥ u / (1 + u)`,
so that `(1 - q)^{-5} ≤ (1 + u)⁵ / u⁵`. This yields `w(y) ≤ (1 + 2πy)⁵ e^{-2πy} / π`;
finally `1 + 2πy ≤ 2π (1 + y)` and `32 π⁴ < 8192` since `π < 4`.

## Main results

* `Zeta5Irr.weight_le`: `w(y) ≤ 8192 (1 + y)⁵ e^{-2πy}` for `y > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For every real `u`, `(1 + u) e^{-u} ≤ 1`. -/
theorem one_add_mul_exp_neg_le_one (u : ℝ) : (1 + u) * rexp (-u) ≤ 1 := by
  calc (1 + u) * rexp (-u) ≤ rexp u * rexp (-u) := by gcongr; linarith [add_one_le_exp u]
    _ = 1 := by simp [← exp_add]

/-- For `u ≥ 0` and `q = e^{-u}`, `u⁵ (1 + 11 q + 11 q² + q³) ≤ 24 ((1 - q) (1 + u))⁵`. -/
theorem pow_five_mul_eulerian_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 5 * (1 + 11 * rexp (-u) + 11 * rexp (-u) ^ 2 + rexp (-u) ^ 3) ≤
      24 * ((1 - rexp (-u)) * (1 + u)) ^ 5 := by
  have hq0 := (exp_pos (-u)).le
  have hq1 : rexp (-u) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hS : 1 + 11 * rexp (-u) + 11 * rexp (-u) ^ 2 + rexp (-u) ^ 3 ≤ 24 := by
    nlinarith [pow_le_one₀ (n := 2) hq0 hq1, pow_le_one₀ (n := 3) hq0 hq1]
  have hu5 : u ^ 5 ≤ ((1 - rexp (-u)) * (1 + u)) ^ 5 :=
    pow_le_pow_left₀ hu (by nlinarith [one_add_mul_exp_neg_le_one u]) 5
  calc _ ≤ ((1 - rexp (-u)) * (1 + u)) ^ 5 * 24 := by gcongr
    _ = _ := by ring

/-- For `y > 0`, the weight is bounded by `w(y) ≤ 8192 (1 + y)⁵ e^{-2πy}`. -/
@[zeta5irr "lem_w_bound"]
theorem weight_le {y : ℝ} (hy : 0 < y) :
    weight y ≤ 8192 * (1 + y) ^ 5 * rexp (-(2 * π * y)) := by
  rw [weight_eq_closed hy]
  set u := 2 * π * y with hu
  set q := rexp (-u) with hq
  have h4 : rexp (-(4 * π * y)) = q ^ 2 := by
    rw [hq, ← exp_nat_mul]
    congr 1
    push_cast
    ring
  have h6 : rexp (-(6 * π * y)) = q ^ 3 := by
    rw [hq, ← exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h4, h6]
  have hpi := pi_pos
  have hu0 : 0 < u := by positivity
  have hq1 : 0 < 1 - q := by linarith [exp_lt_one_iff.mpr (neg_lt_zero.mpr hu0)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have key : (2 * π) ^ 4 * y ^ 5 * (1 + 11 * q + 11 * q ^ 2 + q ^ 3) ≤
      12 * 8192 * (1 + y) ^ 5 * (1 - q) ^ 5 := by
    have e : (2 * π) ^ 4 * y ^ 5 = u ^ 5 / (2 * π) := by
      rw [hu]
      field_simp
    have h1u : 1 + u ≤ 2 * π * (1 + y) := by nlinarith [pi_gt_three]
    calc (2 * π) ^ 4 * y ^ 5 * (1 + 11 * q + 11 * q ^ 2 + q ^ 3)
        ≤ 24 * ((1 - q) * (2 * π * (1 + y))) ^ 5 / (2 * π) := by
          rw [e, div_mul_eq_mul_div]
          gcongr ?_ / _
          exact (pow_five_mul_eulerian_exp_neg_le hu0.le).trans (by gcongr)
      _ = 24 * (2 * π) ^ 4 * (1 + y) ^ 5 * (1 - q) ^ 5 := by field_simp
      _ ≤ 12 * 8192 * (1 + y) ^ 5 * (1 - q) ^ 5 := by
          have : 24 * (2 * π) ^ 4 ≤ 12 * 8192 := by
            nlinarith [pow_le_pow_left₀ hpi.le pi_lt_four.le 4]
          gcongr ?_ * _ * _
  calc (2 * π) ^ 4 * y ^ 5 / 12 * (q * (1 + 11 * q + 11 * q ^ 2 + q ^ 3))
      = q * ((2 * π) ^ 4 * y ^ 5 * (1 + 11 * q + 11 * q ^ 2 + q ^ 3)) / 12 := by ring
    _ ≤ q * (12 * 8192 * (1 + y) ^ 5 * (1 - q) ^ 5) / 12 := by gcongr
    _ = 8192 * (1 + y) ^ 5 * q * (1 - q) ^ 5 := by ring

end Zeta5Irr
