/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.RealRiemannLower
public import Zeta5Irr.RealDeterminant.LogFactorialUpper
public import Zeta5Irr.Measure.VZero
public import Mathlib.Algebra.Order.Star.Real

/-!
# A right-endpoint Riemann sum of `log (t + u²)` exceeds the integral by `O(log K)`

For `1 ≤ m ≤ K` and `t ≥ 0`,
`∑_{j=1}^m log (t + (j/K)²) - K ∫_0^{m/K} log (t + u²) du ≤ 2 log K + 2`.

The defect is largest at `t = 0`: for `0 < u ≤ v` one has
`log (t + v²) - log (t + u²) ≤ log (v²) - log (u²)`, i.e. `u ↦ log (t + u²) - log (u²)` is
antitone on `u > 0`, so its right-endpoint Riemann sum is at most `K` times its integral.
At `t = 0` the defect is computed exactly from `∫_0^x log u du = x log x - x`: it equals
`2 log (m!) - 2 m log m + 2 m`, which is at most `2 log m + 2` by the Stirling-type upper
bound for `log (m!)`.

## Main results

* `Zeta5Irr.log_add_sq_sub_le`: `log (t + v²) - log (t + u²) ≤ log (v²) - log (u²)` for
  `0 < u ≤ v` and `t ≥ 0`.
* `Zeta5Irr.sum_log_add_sq_sub_le_log_sq`: the defect at `t` is at most the defect at `0`.
* `Zeta5Irr.sum_log_sq_sub_integral_eq`: the exact value of the defect at `t = 0`.
* `Zeta5Irr.sum_log_add_sq_sub_integral_le`: the bound `2 log K + 2`.

## Implementation notes

The source takes `K` to be the positive integer `40 n`. Only `1 ≤ m ≤ K` is used, so here `K`
is any real number with `m ≤ K`, and `m ≥ 1` is a natural number.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3: the Gram integral and scaling.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For `0 < u ≤ v` and `t ≥ 0`, adding `t` to both squares shrinks the log-ratio:
`log (t + v²) - log (t + u²) ≤ log (v²) - log (u²)`. -/
theorem log_add_sq_sub_le {t u v : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (huv : u ≤ v) :
    log (t + v ^ 2) - log (t + u ^ 2) ≤ log (v ^ 2) - log (u ^ 2) := by
  have hv : 0 < v := hu.trans_le huv
  rw [← log_div (by positivity) (by positivity), ← log_div (by positivity) (by positivity)]
  apply log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : u ^ 2 ≤ v ^ 2 := by gcongr
  nlinarith

/-- The Riemann-sum defect of `log (t + u²)` is at most the defect at `t = 0`: for `K > 0`,
`m ∈ ℕ` and `t ≥ 0`,
`∑_{j=1}^m log (t + (j/K)²) - K ∫_0^{m/K} log (t + u²) du`
`≤ ∑_{j=1}^m log ((j/K)²) - K ∫_0^{m/K} log (u²) du`. -/
theorem sum_log_add_sq_sub_le_log_sq {K : ℝ} (hK : 0 < K) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ Finset.Icc 1 m, log (t + (j / K) ^ 2) -
        K * ∫ u in (0 : ℝ)..(m / K), log (t + u ^ 2) ≤
      ∑ j ∈ Finset.Icc 1 m, log ((j / K) ^ 2) -
        K * ∫ u in (0 : ℝ)..(m / K), log (u ^ 2) := by
  set h : ℝ → ℝ := fun u => log (t + u ^ 2) - log (u ^ 2) with h_def
  have hint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b := fun a b =>
    (intervalIntegrable_log_add_sq t a b).sub (by simp)
  have key : ∑ j ∈ Finset.Icc 1 m, h (j / K) ≤ K * ∫ u in (0 : ℝ)..(m / K), h u := by
    have := mul_integral_le_sum_right (f := fun u => -h u) hK m (fun a b => (hint a b).neg)
      fun k u hu => by
        have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu.1
        have := log_add_sq_sub_le ht hu0 hu.2.le
        simp only [h_def]
        linarith
    rw [intervalIntegral.integral_neg, Finset.sum_neg_distrib] at this
    linarith
  simp only [h_def, Finset.sum_sub_distrib] at key
  rw [intervalIntegral.integral_sub (intervalIntegrable_log_add_sq t _ _)
    (by simp)] at key
  linarith

/-- The Riemann-sum defect of `log (u²)` is explicit: for `K ≠ 0` and `m ∈ ℕ`,
`∑_{j=1}^m log ((j/K)²) - K ∫_0^{m/K} log (u²) du = 2 log (m!) - 2 m log m + 2 m`. -/
theorem sum_log_sq_sub_integral_eq {K : ℝ} (hK : K ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, log ((j / K) ^ 2) - K * ∫ u in (0 : ℝ)..(m / K), log (u ^ 2) =
      2 * log m.factorial - 2 * m * log m + 2 * m := by
  have hsum : ∑ j ∈ Finset.Icc 1 m, log ((j / K) ^ 2) =
      2 * log m.factorial - 2 * m * log K := by
    have hpos : ∀ j ∈ Finset.Icc 1 m, (j : ℝ) ≠ 0 := fun j hj => by
      have := (Finset.mem_Icc.mp hj).1
      positivity
    rw [Finset.sum_congr rfl fun j hj => by
      rw [log_pow, log_div (hpos j hj) hK, Nat.cast_ofNat, mul_sub]]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← log_prod hpos, Finset.sum_const,
      Nat.card_Icc, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.prod_Ico_id_eq_factorial,
      Nat.cast_prod]
    simp only [nsmul_eq_mul, add_tsub_cancel_right]
    ring
  rw [hsum, integral_log_sq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [log_div hm' hK]
  field_simp
  ring

/-- **Riemann-sum upper bound.** For a natural number `1 ≤ m` and a real `K ≥ m`, and every
`t ≥ 0`, `∑_{j=1}^m log (t + (j/K)²) - K ∫_0^{m/K} log (t + u²) du ≤ 2 log K + 2`. -/
@[zeta5irr "lem_riemann_sum"]
theorem sum_log_add_sq_sub_integral_le {K : ℝ} {m : ℕ} (hm : 1 ≤ m) (hmK : (m : ℝ) ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ Finset.Icc 1 m, log (t + (j / K) ^ 2) -
      K * ∫ u in (0 : ℝ)..(m / K), log (t + u ^ 2) ≤ 2 * log K + 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : 0 < K := by linarith
  refine (sum_log_add_sq_sub_le_log_sq hK m ht).trans ?_
  rw [sum_log_sq_sub_integral_eq hK.ne' m]
  have hf := log_factorial_le m
  have hlog : log m ≤ log K := log_le_log (by linarith) hmK
  linarith

end Zeta5Irr
