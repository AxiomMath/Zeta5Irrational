/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.LogFactorialLower

/-!
# A lower bound for `∑ log ((2i)!)`

For every integer `h ≥ 2`,
`-2 ∑_{i=1}^{h-1} log ((2i)!) ≤ -2 h² log (2h) + 3 h² + 4 h log (2h)`.

## Main results

* `Zeta5Irr.neg_two_mul_sum_log_factorial_two_mul_le`: the displayed inequality.

## Implementation notes

The source compares `∑ i log (2i)` with `∫₀^{h-1} x log (2x) dx` and then passes from `h - 1`
to `h`. We instead argue by induction on `h`. The case `h = 2` reads `-2 log 2 ≤ 12`. For the
step from `h` to `h + 1`, write `L = log (2h)` and `L' = log (2h + 2)`; the lower bound
`log ((2h)!) ≥ 2h log (2h) - 2h + 1` reduces the claim to
`2 (h² - 1) (L' - L) - 2 L ≤ 2h + 5`, which follows from `0 ≤ L' - L ≤ 1/h`
(`log x ≤ x - 1` at `x = (h + 1)/h`) and `L ≥ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (the Gram integral and scaling).
-/

@[expose] public section

namespace Zeta5Irr

open Nat Finset

/-- For every integer `h ≥ 2`,
`-2 ∑_{i=1}^{h-1} log ((2i)!) ≤ -2 h² log (2h) + 3 h² + 4 h log (2h)`. -/
@[zeta5irr "lem_real_sum_log2i"]
theorem neg_two_mul_sum_log_factorial_two_mul_le {h : ℕ} (hh : 2 ≤ h) :
    -2 * ∑ i ∈ Ico 1 h, Real.log ((2 * i)! : ℝ) ≤
      -2 * (h : ℝ) ^ 2 * Real.log (2 * h) + 3 * (h : ℝ) ^ 2 + 4 * h * Real.log (2 * h) := by
  induction h, hh using Nat.le_induction with
  | base =>
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    norm_num [Finset.sum_Ico_succ_top]
    linarith
  | succ h hh ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hF := mul_log_sub_add_one_le_log_factorial (m := 2 * h) (by omega)
    push_cast at hF ⊢
    have hh' : (2 : ℝ) ≤ h := by exact_mod_cast hh
    have hL : 0 ≤ Real.log (2 * h) := Real.log_nonneg (by linarith)
    have hsplit : Real.log (2 * (h + 1)) = Real.log (2 * h) + Real.log ((h + 1) / h) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hd : Real.log (((h : ℝ) + 1) / h) ≤ 1 / h := by
      have := Real.log_le_sub_one_of_pos (x := ((h : ℝ) + 1) / h) (by positivity)
      have e : ((h : ℝ) + 1) / h - 1 = 1 / h := by field_simp; ring
      linarith
    have hd0 : 0 ≤ Real.log (((h : ℝ) + 1) / h) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
    have hd' : (h : ℝ) * Real.log (((h : ℝ) + 1) / h) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hd
      linarith
    have key : ((h : ℝ) ^ 2 - 1) * Real.log (((h : ℝ) + 1) / h) ≤ h := by
      nlinarith [mul_le_mul_of_nonneg_left hd' (by positivity : (0 : ℝ) ≤ h)]
    rw [hsplit]
    nlinarith

end Zeta5Irr
