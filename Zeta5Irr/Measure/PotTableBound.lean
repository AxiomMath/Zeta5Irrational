/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.EncLogSpec
public import Zeta5Irr.Measure.EncAtanSpec
public import Zeta5Irr.Measure.ArcsinePotential
public import Zeta5Irr.Measure.PotArcsineOff
public import Zeta5Irr.Measure.RhoSupport
public import Zeta5Irr.Measure.PotBound
public import Zeta5Irr.Measure.PotInterval
public import Zeta5Irr.Measure.VFormula
public import Zeta5Irr.Measure.RhoPotMonoRight
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The interval bound on the refinement table

For every triple `(j, d, k)` of the refinement table `𝒯`, the interval bound on the dyadic cell
`J_{j,d,k} = [l, r]`, `l = Aⱼ + (Aⱼ₊₁ - Aⱼ) k / 2^d`, `r = Aⱼ + (Aⱼ₊₁ - Aⱼ) (k + 1) / 2^d`,
satisfies `𝓑(l, r) < -6645002 / 10⁶`.

Both endpoints are rational. The bound `𝓑(l, r) = 2 max (U^ρ(l), U^ρ(r)) - W` has three kinds of
ingredients. The potential `U^ρ(x) = ∑ᵢ cᵢ U^{ω_{[aᵢ,bᵢ]}}(x)` is a combination of logarithms:
`log ((bᵢ - aᵢ)/4)` when `aᵢ ≤ x ≤ bᵢ`, and
`log ((|x - (aᵢ + bᵢ)/2| + √((x - aᵢ)(x - bᵢ)))/2)` otherwise. The subtracted term `W` is `V(r)`,
`V(l)` or `V_*`, each given by the closed form of the external field, a combination of
logarithms, square roots, arctangents and `π`. Every one of these is enclosed between rationals:
square roots by integer square roots, logarithms by the series `Λ_m` of
`log ((1 + z)/(1 - z))` after the reduction `log (2^e r) = e log 2 + log r` with `1 ≤ r < 2`,
arctangents by the truncated series `T_m` after the reductions `arctan x = π/2 - arctan (1/x)`
and `arctan x = arctan (1/2) + arctan ((2x - 1)/(2 + x))`, and `π` by its decimal enclosure. The
bound is then evaluated in directed interval arithmetic, each operation rounded in the direction
that keeps the result an upper bound for `𝓑(l, r)`, and the resulting finite statement over the
`684` cells is decided by evaluation in the kernel.

## Main results

* `Zeta5Irr.potBound_potInterval_lt`: `𝓑(l, r) < -6645002 / 10⁶` on every cell of `𝒯`.

## Implementation notes

* All enclosures are carried out in fixed point: an integer `n` stands for `n / 2^64`, and each
  division is rounded down (`Zeta5Irr.PotTableBound.fdiv`) or up
  (`Zeta5Irr.PotTableBound.cdiv`) as the direction of the enclosure requires. Points of the
  grid, cells and table entries are exact: a point of `J_{j,d,k}` is an integer over
  `10¹² 2^d`, so every case distinction (whether `x ∈ [aᵢ, bᵢ]`, whether `r ≤ q₋`, whether
  `q₊ ≤ l`) is an exact integer comparison.
* The source prescribes `m = 64` logarithm terms, `m = 80` arctangent terms and an accuracy of
  `2^{-144}`; far less suffices. Here `Λ_{22}` is used on `0 ≤ z ≤ 1/3` and `T_{32}` on
  `0 ≤ z ≤ 1/2`, where both remainders are below `2^{-64}`, and the arctangent is reduced to
  `[0, 1/2]` by the addition formula with `arctan (1/2)` rather than by the half-angle
  formula, which would need a further square root. The series are evaluated by Horner's rule
  with directed rounding, the alternating series of the arctangent as the difference of its
  two positive halves.
* The constant `π` is enclosed by Mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20` rather than
  by Machin's formula; `log 2` and `arctan (1/2)` are enclosed by the same series.
* The source writes the potential of `ρ` as the sum of those of its sixteen components; this
  is `Zeta5Irr.logPotential_rho_eq_sum`.
* The table is checked row by row: along a row, the bound for `U^ρ` at the common endpoint of
  two consecutive cells is computed once. The rows are decided in chunks of eight, which keeps
  the memory of each kernel evaluation bounded.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6: the interval bound and the partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr.PotTableBound

open Finset Real

/-- The fixed-point scale `2^64`: an integer `n` stands for the real number `n / 2^64`. -/
def S : ℤ := 18446744073709551616
/-- Division rounded down, `⌊a / b⌋` for `b > 0`. -/
def fdiv (a b : ℤ) : ℤ := a / b
/-- Division rounded up, `⌈a / b⌉` for `b > 0`. -/
def cdiv (a b : ℤ) : ℤ := -((-a) / b)

/-- The scale `2^64` is positive. -/
theorem S_pos : (0 : ℤ) < S := by decide
/-- The scale `S` is `2^64` as a real number. -/
theorem S_cast : (S : ℝ) = 2 ^ 64 := by norm_num [S]
/-- The scale `S` is positive as a real number. -/
theorem S_real_pos : (0 : ℝ) < S := by exact_mod_cast S_pos

/-- Rounding down: `fdiv a b ≤ a / b` for `b > 0`. -/
theorem fdiv_le (a : ℤ) {b : ℤ} (hb : 0 < b) : (fdiv a b : ℝ) ≤ a / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

/-- Rounding up: `a / b ≤ cdiv a b` for `b > 0`. -/
theorem le_cdiv (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  have := fdiv_le (-a) hb
  simp only [fdiv, cdiv] at *
  push_cast at *
  rw [neg_div] at this
  linarith

/-- `fdiv a b` is nonnegative when `a ≥ 0` and `b > 0`. -/
theorem fdiv_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ fdiv a b :=
  Int.ediv_nonneg ha hb.le

/-- `cdiv a b` is nonnegative when `a ≥ 0` and `b > 0`. -/
theorem cdiv_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ cdiv a b := by
  have := le_cdiv a hb
  have h : (0 : ℝ) ≤ a / b := div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le)
  exact_mod_cast h.trans this

/-! ### Horner evaluation with directed rounding -/

/-- `Σ_{i<n} v^i / (a (s + i) + b)`, by Horner's rule. -/
noncomputable def hornR (a b : ℕ) (v : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, s => 1 / (a * s + b : ℝ) + v * hornR a b v n (s + 1)

/-- Horner's rule for `2^64 ∑_{i<n} v^i / (a (s + i) + b)` rounded up, from an upper bound
`V` for `2^64 v`. -/
def hornU (a b : ℕ) (V : ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | n + 1, s => cdiv S (a * s + b : ℕ) + cdiv (V * hornU a b V n (s + 1)) S

/-- Horner's rule for `2^64 ∑_{i<n} v^i / (a (s + i) + b)` rounded down, from a lower
bound `V` for `2^64 v`. -/
def hornL (a b : ℕ) (V : ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | n + 1, s => fdiv S (a * s + b : ℕ) + fdiv (V * hornL a b V n (s + 1)) S

/-- The Horner evaluation `hornR a b v n s` equals `∑_{i<n} v^i / (a (s + i) + b)`. -/
theorem hornR_eq_sum (a b : ℕ) (v : ℝ) (n s : ℕ) :
    hornR a b v n s = ∑ i ∈ range n, v ^ i / (a * (s + i : ℕ) + b : ℝ) := by
  induction n generalizing s with
  | zero => simp [hornR]
  | succ n ih =>
    rw [hornR, ih, sum_range_succ', mul_sum]
    simp only [pow_zero, add_zero, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s + 1 + i = s + (i + 1) by ring]
    ring

/-- `hornR a b v n s` is nonnegative for `v ≥ 0`. -/
theorem hornR_nonneg (a b : ℕ) {v : ℝ} (hv : 0 ≤ v) (n s : ℕ) : 0 ≤ hornR a b v n s := by
  induction n generalizing s with
  | zero => simp [hornR]
  | succ n ih =>
    rw [hornR]
    have := ih (s + 1)
    positivity

/-- If `V` is an upper bound for `2^64 v` with `v ≥ 0`, then `hornU a b V n s` is an upper
bound for `2^64 hornR a b v n s`. -/
theorem hornR_le_hornU {a b : ℕ} (hb : 0 < b) {v : ℝ} {V : ℤ} (hv : 0 ≤ v)
    (hV : v * S ≤ V) (n s : ℕ) : hornR a b v n s * S ≤ hornU a b V n s := by
  induction n generalizing s with
  | zero => simp [hornR, hornU]
  | succ n ih =>
    have hd : (0 : ℤ) < (a * s + b : ℕ) := by exact_mod_cast (by omega : 0 < a * s + b)
    have h1 := le_cdiv S hd
    have h2 := le_cdiv (V * hornU a b V n (s + 1)) S_pos
    have hH := hornR_nonneg a b hv n (s + 1)
    have ih' := ih (s + 1)
    have hS := S_real_pos
    have hVn : (0 : ℝ) ≤ V := (mul_nonneg hv hS.le).trans hV
    have key : v * S * (hornR a b v n (s + 1) * S) ≤ V * hornU a b V n (s + 1) := by
      exact_mod_cast mul_le_mul hV ih' (mul_nonneg hH hS.le) hVn
    simp only [hornR, hornU]
    push_cast at h1 h2 ⊢
    have e1 : 1 / ((a : ℝ) * s + b) * S = S / (a * s + b) := by ring
    have e2 : v * hornR a b v n (s + 1) * S = v * S * (hornR a b v n (s + 1) * S) / S := by
      field_simp
    rw [add_mul, e1, e2]
    exact add_le_add h1 ((div_le_div_of_nonneg_right key hS.le).trans h2)

/-- `hornL a b V n s` is nonnegative for `V ≥ 0`. -/
theorem hornL_nonneg {a b : ℕ} {V : ℤ} (hV : 0 ≤ V) (n s : ℕ) : 0 ≤ hornL a b V n s := by
  induction n generalizing s with
  | zero => simp [hornL]
  | succ n ih =>
    simp only [hornL]
    have hd : (0 : ℤ) ≤ (a * s + b : ℕ) := by positivity
    exact add_nonneg (Int.ediv_nonneg S_pos.le hd) (fdiv_nonneg (mul_nonneg hV (ih _)) S_pos)

/-- If `0 ≤ V` is a lower bound for `2^64 v`, then `hornL a b V n s` is a lower bound for
`2^64 hornR a b v n s`. -/
theorem hornL_le_hornR {a b : ℕ} (hb : 0 < b) {v : ℝ} {V : ℤ} (hV0 : 0 ≤ V)
    (hV : (V : ℝ) ≤ v * S) (n s : ℕ) : (hornL a b V n s : ℝ) ≤ hornR a b v n s * S := by
  induction n generalizing s with
  | zero => simp [hornR, hornL]
  | succ n ih =>
    have hd : (0 : ℤ) < (a * s + b : ℕ) := by exact_mod_cast (by omega : 0 < a * s + b)
    have h1 := fdiv_le S hd
    have h2 := fdiv_le (V * hornL a b V n (s + 1)) S_pos
    have hH := hornL_nonneg (a := a) (b := b) hV0 n (s + 1)
    have ih' := ih (s + 1)
    have hS := S_real_pos
    have hv : 0 ≤ v * S := (by exact_mod_cast hV0 : (0:ℝ) ≤ V).trans hV
    have key : (V : ℝ) * hornL a b V n (s + 1) ≤ v * S * (hornR a b v n (s + 1) * S) :=
      mul_le_mul hV ih' (by exact_mod_cast hH) hv
    simp only [hornR, hornL]
    push_cast at h1 h2 ⊢
    have e1 : 1 / ((a : ℝ) * s + b) * S = S / (a * s + b) := by ring
    have e2 : v * hornR a b v n (s + 1) * S = v * S * (hornR a b v n (s + 1) * S) / S := by
      field_simp
    rw [add_mul, e1, e2]
    exact add_le_add h1 (h2.trans (div_le_div_of_nonneg_right key hS.le))


/-! ### The logarithm -/

/-- The series `Λ_m(z)` equals `2 z ∑_{i<m} z^{2i} / (2i + 1)` in Horner form. -/
theorem logApprox_eq_hornR (m : ℕ) (z : ℝ) :
    logApprox m z = 2 * z * hornR 2 1 (z ^ 2) m 0 := by
  simp only [logApprox, hornR_eq_sum, mul_assoc, mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [← pow_mul, pow_succ, zero_add]
  ring

/-- An upper bound for `2^64 log ((1 + z) / (1 - z))`, `z = N / D ∈ [0, 1/3]`: the series
`Λ₂₂(z)` rounded up, plus one unit for the remainder. -/
def logSerU (N D : ℤ) : ℤ :=
  2 * cdiv (cdiv (N * S) D * hornU 2 1 (cdiv (N * N * S) (D * D)) 22 0) S + 1

/-- A lower bound for `2^64 log ((1 + z) / (1 - z))`, `z = N / D ∈ [0, 1)`: the series
`Λ₂₂(z)` rounded down. -/
def logSerL (N D : ℤ) : ℤ :=
  2 * fdiv (fdiv (N * S) D * hornL 2 1 (fdiv (N * N * S) (D * D)) 22 0) S

/-- For `0 ≤ z ≤ 1/3`, the remainder bound `2 z^{45} / (45 (1 - z²))` of `Λ₂₂(z)` is at most
`2^{-64}`. -/
theorem log_rem_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 3) :
    2 * z ^ (2 * 22 + 1) / ((2 * (22 : ℕ) + 1) * (1 - z ^ 2)) ≤ 1 / 2 ^ 64 := by
  have hz2 : z ^ 2 ≤ 1 / 9 := by nlinarith
  have hp : z ^ (2 * 22 + 1) ≤ (1 / 3) ^ (2 * 22 + 1) := pow_le_pow_left₀ h0 h1 _
  calc 2 * z ^ (2 * 22 + 1) / ((2 * (22 : ℕ) + 1) * (1 - z ^ 2))
      ≤ 2 * (1 / 3) ^ (2 * 22 + 1) / ((2 * (22 : ℕ) + 1) * (1 - 1 / 9)) := by
        gcongr
    _ ≤ 1 / 2 ^ 64 := by norm_num

/-- For `z = N / D ∈ [0, 1/3]`, `2^64 log ((1 + z) / (1 - z)) ≤ logSerU N D`. -/
theorem log_le_logSerU {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (h3 : 3 * N ≤ D) :
    Real.log ((1 + N / D) / (1 - N / D)) * S ≤ logSerU N D := by
  set z : ℝ := N / D with hz
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hz0 : 0 ≤ z := div_nonneg (by exact_mod_cast hN) hDr.le
  have hz3 : z ≤ 1 / 3 := by
    rw [hz, div_le_iff₀ hDr]
    have : (3 * N : ℝ) ≤ D := by exact_mod_cast h3
    linarith
  have hS := S_real_pos
  have hrem := log_rem_le hz0 hz3
  have hlog := log_sub_logApprox_le hz0 (by linarith) 22
  push_cast at hlog
  rw [logApprox_eq_hornR] at hlog
  set V := cdiv (N * N * S) (D * D)
  set Z := cdiv (N * S) D
  have hV : z ^ 2 * S ≤ V := by
    have := le_cdiv (N * N * S) (mul_pos hD hD)
    push_cast at this
    calc z ^ 2 * S = N * N * S / (D * D) := by rw [hz]; field_simp
      _ ≤ _ := this
  have hZ : z * S ≤ Z := by
    have := le_cdiv (N * S) hD
    push_cast at this
    calc z * S = N * S / D := by rw [hz]; field_simp
      _ ≤ _ := this
  have hH := hornR_le_hornU (a := 2) one_pos (sq_nonneg z) hV 22 0
  have hHn := hornR_nonneg 2 1 (sq_nonneg z) 22 0
  have key : z * S * (hornR 2 1 (z ^ 2) 22 0 * S) ≤ Z * hornU 2 1 V 22 0 :=
    mul_le_mul hZ hH (by positivity) ((mul_nonneg hz0 hS.le).trans hZ)
  have hc := le_cdiv (Z * hornU 2 1 V 22 0) S_pos
  push_cast at hc
  unfold logSerU
  push_cast
  have e : 2 * z * hornR 2 1 (z ^ 2) 22 0 * S =
      2 * (z * S * (hornR 2 1 (z ^ 2) 22 0 * S) / S) := by field_simp
  have h4 : Real.log ((1 + z) / (1 - z)) * S ≤
      (2 * z * hornR 2 1 (z ^ 2) 22 0 + 1 / 2 ^ 64) * S := by
    gcongr; linarith
  rw [add_mul, e, S_cast] at h4
  rw [S_cast] at hc key ⊢
  have : 1 / (2 : ℝ) ^ 64 * 2 ^ 64 = 1 := by norm_num
  rw [this] at h4
  have h5 := div_le_div_of_nonneg_right key (by positivity : (0 : ℝ) ≤ 2 ^ 64)
  linarith

/-- For `z = N / D ∈ [0, 1)`, `logSerL N D ≤ 2^64 log ((1 + z) / (1 - z))`. -/
theorem logSerL_le_log {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (h1 : N < D) :
    (logSerL N D : ℝ) ≤ Real.log ((1 + N / D) / (1 - N / D)) * S := by
  set z : ℝ := N / D with hz
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hz0 : 0 ≤ z := div_nonneg (by exact_mod_cast hN) hDr.le
  have hz1 : z < 1 := by
    rw [hz, div_lt_iff₀ hDr, one_mul]; exact_mod_cast h1
  have hS := S_real_pos
  have hlog := logApprox_le_log hz0 hz1 22
  rw [logApprox_eq_hornR] at hlog
  set V := fdiv (N * N * S) (D * D)
  set Z := fdiv (N * S) D
  have hV0 : 0 ≤ V := fdiv_nonneg (mul_nonneg (mul_self_nonneg N) S_pos.le) (mul_pos hD hD)
  have hZ0 : 0 ≤ Z := fdiv_nonneg (mul_nonneg hN S_pos.le) hD
  have hV : (V : ℝ) ≤ z ^ 2 * S := by
    have := fdiv_le (N * N * S) (mul_pos hD hD)
    push_cast at this
    calc _ ≤ _ := this
      _ = z ^ 2 * S := by rw [hz]; field_simp
  have hZ : (Z : ℝ) ≤ z * S := by
    have := fdiv_le (N * S) hD
    push_cast at this
    calc _ ≤ _ := this
      _ = z * S := by rw [hz]; field_simp
  have hH := hornL_le_hornR (a := 2) one_pos hV0 hV 22 0
  have hHn := hornL_nonneg (a := 2) (b := 1) hV0 22 0
  have key : (Z : ℝ) * hornL 2 1 V 22 0 ≤ z * S * (hornR 2 1 (z ^ 2) 22 0 * S) :=
    mul_le_mul hZ hH (by exact_mod_cast hHn) (mul_nonneg hz0 hS.le)
  have hc := fdiv_le (Z * hornL 2 1 V 22 0) S_pos
  push_cast at hc
  unfold logSerL
  push_cast
  have e : 2 * z * hornR 2 1 (z ^ 2) 22 0 * S =
      2 * (z * S * (hornR 2 1 (z ^ 2) 22 0 * S) / S) := by field_simp
  have h4 := mul_le_mul_of_nonneg_right hlog hS.le
  rw [e] at h4
  have h5 := div_le_div_of_nonneg_right key hS.le
  linarith


/-- A lower bound for `2^64 log 2`. -/
def log2Lo : ℤ := 12786308645202655658
/-- An upper bound for `2^64 log 2`. -/
def log2Hi : ℤ := 12786308645202655663

/-- The value of `logSerL 1 3` is `log2Lo`. -/
theorem logSerL_one_three : logSerL 1 3 = log2Lo := by decide +kernel
/-- The value of `logSerU 1 3` is `log2Hi`. -/
theorem logSerU_one_three : logSerU 1 3 = log2Hi := by decide +kernel

/-- `log2Lo ≤ 2^64 log 2`. -/
theorem log2Lo_le : (log2Lo : ℝ) ≤ Real.log 2 * S := by
  have := logSerL_le_log (N := 1) (D := 3) (by norm_num) (by norm_num) (by norm_num)
  rw [logSerL_one_three] at this
  convert this using 3
  norm_num

/-- `2^64 log 2 ≤ log2Hi`. -/
theorem le_log2Hi : Real.log 2 * S ≤ log2Hi := by
  have := log_le_logSerU (N := 1) (D := 3) (by norm_num) (by norm_num) (by norm_num)
  rw [logSerU_one_three] at this
  convert this using 3
  norm_num

/-- Binary search for the integer part of `log₂ Y`, `i` bits at a time. -/
def lg2Aux (Y : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | i + 1, k => lg2Aux Y i (if 2 ^ (k + 2 ^ i) ≤ Y then k + 2 ^ i else k)

/-- The integer part of `log₂ Y`, for `0 < Y < 2^1024`. -/
def lg2 (Y : ℕ) : ℕ := lg2Aux Y 10 0

/-- An upper bound for `2^64 log (Y / 2^64)`: with `2^k ≤ Y < 2^{k+1}`,
`log (Y / 2^64) = log (Y / 2^k) + (k - 64) log 2`, and `Y / 2^k = (1 + z)/(1 - z)` with
`z = (Y - 2^k)/(Y + 2^k) ∈ [0, 1/3)`. If the range reduction fails, `log y ≤ y - 1` is used. -/
def logU (Y : ℤ) : ℤ :=
  let k := lg2 Y.toNat
  let T : ℤ := 2 ^ k
  if T ≤ Y ∧ Y < 2 * T then
    logSerU (Y - T) (Y + T) + ((k : ℤ) - 64) * (if 64 ≤ k then log2Hi else log2Lo)
  else Y

/-- A lower bound for `2^64 log (Y / 2^64)`, by the same range reduction as
`Zeta5Irr.PotTableBound.logU`; if the reduction fails, `1 - 1/y ≤ log y` is used. -/
def logL (Y : ℤ) : ℤ :=
  let k := lg2 Y.toNat
  let T : ℤ := 2 ^ k
  if T ≤ Y ∧ Y < 2 * T then
    logSerL (Y - T) (Y + T) + ((k : ℤ) - 64) * (if 64 ≤ k then log2Lo else log2Hi)
  else fdiv (S * (Y - S)) Y

/-- For `Y > 0`, `log (Y / 2^64) = log ((1 + z) / (1 - z)) + (k - 64) log 2` with
`z = (Y - 2^k) / (Y + 2^k)`. -/
theorem log_div_S_eq {Y : ℤ} (k : ℕ) (hY : 0 < Y) :
    Real.log (Y / S) = Real.log ((1 + ((Y - 2 ^ k : ℤ) : ℝ) / ((Y + 2 ^ k : ℤ) : ℝ)) /
      (1 - ((Y - 2 ^ k : ℤ) : ℝ) / ((Y + 2 ^ k : ℤ) : ℝ))) + ((k : ℝ) - 64) * Real.log 2 := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hT : (0 : ℝ) < 2 ^ k := by positivity
  have e : (1 + ((Y - 2 ^ k : ℤ) : ℝ) / ((Y + 2 ^ k : ℤ) : ℝ)) /
      (1 - ((Y - 2 ^ k : ℤ) : ℝ) / ((Y + 2 ^ k : ℤ) : ℝ)) = Y / 2 ^ k := by
    push_cast
    have : (Y : ℝ) + 2 ^ k ≠ 0 := by positivity
    field_simp
    ring
  rw [e, S_cast, Real.log_div hYr.ne' (by positivity), Real.log_div hYr.ne' hT.ne',
    Real.log_pow, Real.log_pow]
  ring

/-- If `0 < y` and `2^64 y ≤ Y`, then `2^64 log y ≤ logU Y`. -/
theorem log_mul_S_le_logU {y : ℝ} {Y : ℤ} (hy : 0 < y) (hyY : y * S ≤ Y) :
    Real.log y * S ≤ logU Y := by
  have hS := S_real_pos
  have hYr : (0 : ℝ) < Y := (mul_pos hy hS).trans_le hyY
  have hY : 0 < Y := by exact_mod_cast hYr
  have hle : Real.log y ≤ Real.log (Y / S) :=
    Real.log_le_log hy (by rw [le_div_iff₀ hS]; exact hyY)
  refine (mul_le_mul_of_nonneg_right hle hS.le).trans ?_
  unfold logU
  simp only
  split_ifs with h h64
  · rw [log_div_S_eq (lg2 Y.toNat) hY, add_mul]
    have h1 := log_le_logSerU (N := Y - 2 ^ lg2 Y.toNat) (D := Y + 2 ^ lg2 Y.toNat)
      (by linarith [h.1]) (by positivity) (by linarith [h.2])
    have h2 : ((lg2 Y.toNat : ℝ) - 64) * Real.log 2 * S ≤
        ((lg2 Y.toNat : ℝ) - 64) * log2Hi := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left le_log2Hi (by
        have : (64 : ℝ) ≤ lg2 Y.toNat := by exact_mod_cast h64
        linarith)
    push_cast at h1 ⊢
    linarith
  · rw [log_div_S_eq (lg2 Y.toNat) hY, add_mul]
    have h1 := log_le_logSerU (N := Y - 2 ^ lg2 Y.toNat) (D := Y + 2 ^ lg2 Y.toNat)
      (by linarith [h.1]) (by positivity) (by linarith [h.2])
    have h2 : ((lg2 Y.toNat : ℝ) - 64) * Real.log 2 * S ≤
        ((lg2 Y.toNat : ℝ) - 64) * log2Lo := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonpos_left log2Lo_le (by
        have : (lg2 Y.toNat : ℝ) < 64 := by exact_mod_cast not_le.1 h64
        linarith)
    push_cast at h1 ⊢
    linarith
  · have := Real.log_le_sub_one_of_pos (div_pos hYr hS)
    have e : ((Y : ℝ) / S - 1) * S = Y - S := by field_simp
    nlinarith

/-- If `0 < Y ≤ 2^64 y`, then `logL Y ≤ 2^64 log y`. -/
theorem logL_le_log_mul_S {y : ℝ} {Y : ℤ} (hY : 0 < Y) (hyY : (Y : ℝ) ≤ y * S) :
    (logL Y : ℝ) ≤ Real.log y * S := by
  have hS := S_real_pos
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hle : Real.log (Y / S) ≤ Real.log y :=
    Real.log_le_log (div_pos hYr hS) (by rw [div_le_iff₀ hS]; exact hyY)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hle hS.le)
  unfold logL
  simp only
  split_ifs with h h64
  · rw [log_div_S_eq (lg2 Y.toNat) hY, add_mul]
    have h1 := logSerL_le_log (N := Y - 2 ^ lg2 Y.toNat) (D := Y + 2 ^ lg2 Y.toNat)
      (by linarith [h.1]) (by positivity)
      (by linarith [(by positivity : (0 : ℤ) < 2 ^ lg2 Y.toNat)])
    have h2 : ((lg2 Y.toNat : ℝ) - 64) * log2Lo ≤
        ((lg2 Y.toNat : ℝ) - 64) * Real.log 2 * S := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left log2Lo_le (by
        have : (64 : ℝ) ≤ lg2 Y.toNat := by exact_mod_cast h64
        linarith)
    push_cast at h1 ⊢
    linarith
  · rw [log_div_S_eq (lg2 Y.toNat) hY, add_mul]
    have h1 := logSerL_le_log (N := Y - 2 ^ lg2 Y.toNat) (D := Y + 2 ^ lg2 Y.toNat)
      (by linarith [h.1]) (by positivity)
      (by linarith [(by positivity : (0 : ℤ) < 2 ^ lg2 Y.toNat)])
    have h2 : ((lg2 Y.toNat : ℝ) - 64) * log2Hi ≤
        ((lg2 Y.toNat : ℝ) - 64) * Real.log 2 * S := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonpos_left le_log2Hi (by
        have : (lg2 Y.toNat : ℝ) < 64 := by exact_mod_cast not_le.1 h64
        linarith)
    push_cast at h1 ⊢
    linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hYr hS)
    have h2 := fdiv_le (S * (Y - S)) hY
    have e : ((S : ℝ) * (Y - S)) / Y = (1 - ((Y : ℝ) / S)⁻¹) * S := by field_simp
    push_cast at h2
    rw [e] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h1 hS.le)


/-! ### The arctangent -/

/-- If `0 ≤ x ≤ X` and `0 ≤ y ≤ Y`, then `x y / 2^64 ≤ cdiv (X Y) 2^64`. -/
theorem mul_div_S_le_cdiv {x y : ℝ} {X Y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hX : x ≤ X)
    (hY : y ≤ Y) : x * y / S ≤ cdiv (X * Y) S := by
  have h := le_cdiv (X * Y) S_pos
  push_cast at h
  exact (div_le_div_of_nonneg_right (mul_le_mul hX hY hy (hx.trans hX)) S_real_pos.le).trans h

/-- If `0 ≤ X ≤ x` and `0 ≤ Y ≤ y`, then `fdiv (X Y) 2^64 ≤ x y / 2^64`. -/
theorem fdiv_le_mul_div_S {x y : ℝ} {X Y : ℤ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : (X : ℝ) ≤ x)
    (hY : (Y : ℝ) ≤ y) : (fdiv (X * Y) S : ℝ) ≤ x * y / S := by
  have h := fdiv_le (X * Y) S_pos
  push_cast at h
  have hY0' : (0 : ℝ) ≤ Y := by exact_mod_cast hY0
  have hX0' : (0 : ℝ) ≤ X := by exact_mod_cast hX0
  exact h.trans (div_le_div_of_nonneg_right (mul_le_mul hX hY hY0' (hX0'.trans hX))
    S_real_pos.le)

/-- `(N / D)^j · S ≤ ⌈N^j S / D^j⌉`. -/
theorem pow_mul_S_le_cdiv {N D : ℤ} (hD : 0 < D) (j : ℕ) :
    ((N : ℝ) / D) ^ j * S ≤ cdiv (N ^ j * S) (D ^ j) := by
  have h := le_cdiv (N ^ j * S) (pow_pos hD j)
  push_cast at h
  rwa [div_pow, div_mul_eq_mul_div]

/-- `⌊N^j S / D^j⌋ ≤ (N / D)^j · S`. -/
theorem fdiv_le_pow_mul_S {N D : ℤ} (hD : 0 < D) (j : ℕ) :
    (fdiv (N ^ j * S) (D ^ j) : ℝ) ≤ ((N : ℝ) / D) ^ j * S := by
  have h := fdiv_le (N ^ j * S) (pow_pos hD j)
  push_cast at h
  rwa [div_pow, div_mul_eq_mul_div]

/-- The series `T_{2n}(w)` equals the difference of its two positive halves,
`w ∑_{i<n} w^{4i} / (4i + 1) - w³ ∑_{i<n} w^{4i} / (4i + 3)`. -/
theorem atanApprox_two_mul (n : ℕ) (w : ℝ) :
    atanApprox (2 * n) w = w * hornR 4 1 (w ^ 4) n 0 - w ^ 3 * hornR 4 3 (w ^ 4) n 0 := by
  induction n with
  | zero => simp [hornR]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, atanApprox_succ, atanApprox_succ, ih]
    simp only [hornR_eq_sum, sum_range_succ]
    have h1 : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul]; simp
    have h2 : (-1 : ℝ) ^ (2 * n + 1) = -1 := by rw [pow_succ, h1]; simp
    rw [h1, h2]
    push_cast
    ring

/-- For `0 ≤ w ≤ 1/2`, the remainder bound `|w|^{65} / 65` of `T₃₂(w)` is at most `2^{-64}`. -/
theorem atan_rem_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1 / 2) :
    |w| ^ (2 * (2 * 16) + 1) / (2 * ((2 * 16 : ℕ) : ℝ) + 1) ≤ 1 / 2 ^ 64 := by
  rw [abs_of_nonneg h0]
  calc w ^ (2 * (2 * 16) + 1) / (2 * ((2 * 16 : ℕ) : ℝ) + 1)
      ≤ (1 / 2) ^ (2 * (2 * 16) + 1) / (2 * ((2 * 16 : ℕ) : ℝ) + 1) := by gcongr
    _ ≤ 1 / 2 ^ 64 := by norm_num

/-- An upper bound for `2^64 arctan w`, `w = N / D ∈ [0, 1/2]`: the series
`T₃₂(w) = w ∑_{j<16} w^{4j}/(4j+1) - w³ ∑_{j<16} w^{4j}/(4j+3)`, rounded up, plus one unit for
the remainder. -/
def atanSerU (N D : ℤ) : ℤ :=
  cdiv (cdiv (N * S) D * hornU 4 1 (cdiv (N ^ 4 * S) (D ^ 4)) 16 0) S -
    fdiv (fdiv (N ^ 3 * S) (D ^ 3) * hornL 4 3 (fdiv (N ^ 4 * S) (D ^ 4)) 16 0) S + 1

/-- A lower bound for `2^64 arctan w`, `w = N / D ∈ [0, 1/2]`, as in
`Zeta5Irr.PotTableBound.atanSerU`. -/
def atanSerL (N D : ℤ) : ℤ :=
  fdiv (fdiv (N * S) D * hornL 4 1 (fdiv (N ^ 4 * S) (D ^ 4)) 16 0) S -
    cdiv (cdiv (N ^ 3 * S) (D ^ 3) * hornU 4 3 (cdiv (N ^ 4 * S) (D ^ 4)) 16 0) S - 1

/-- For `w = N / D ∈ [0, 1/2]`, `2^64 arctan w ≤ atanSerU N D`. -/
theorem arctan_le_atanSerU {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (h2 : 2 * N ≤ D) :
    Real.arctan (N / D) * S ≤ atanSerU N D := by
  set w : ℝ := N / D with hw
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hw0 : 0 ≤ w := div_nonneg (by exact_mod_cast hN) hDr.le
  have hw2 : w ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ hDr]
    have : (2 * N : ℝ) ≤ D := by exact_mod_cast h2
    linarith
  have hS := S_real_pos
  have habs : |w| < 1 := (abs_of_nonneg hw0).trans_lt (by linarith)
  have hT := abs_arctan_sub_atanApprox_le habs (2 * 16)
  have hrem := atan_rem_le hw0 hw2
  rw [atanApprox_two_mul] at hT
  have hup := (abs_le.1 (hT.trans hrem)).2
  have hV4U := pow_mul_S_le_cdiv (N := N) hD 4
  have hV4L := fdiv_le_pow_mul_S (N := N) hD 4
  have hW1U := pow_mul_S_le_cdiv (N := N) hD 1
  have hW3L := fdiv_le_pow_mul_S (N := N) hD 3
  simp only [pow_one] at hW1U
  rw [← hw] at hV4U hV4L hW1U hW3L
  have hN4 : 0 ≤ N ^ 4 * S := mul_nonneg (pow_nonneg hN 4) S_pos.le
  have hN3 : 0 ≤ N ^ 3 * S := mul_nonneg (pow_nonneg hN 3) S_pos.le
  have hV4L0 := fdiv_nonneg hN4 (pow_pos hD 4)
  have hW3L0 := fdiv_nonneg hN3 (pow_pos hD 3)
  have hE := hornR_le_hornU (a := 4) one_pos (by positivity : (0 : ℝ) ≤ w ^ 4) hV4U 16 0
  have hO := hornL_le_hornR (a := 4) (b := 3) (by norm_num) hV4L0 hV4L 16 0
  have hOn := hornL_nonneg (a := 4) (b := 3) hV4L0 16 0
  have hEr := hornR_nonneg 4 1 (by positivity : (0 : ℝ) ≤ w ^ 4) 16 0
  have h1 := mul_div_S_le_cdiv (mul_nonneg hw0 hS.le) (mul_nonneg hEr hS.le) hW1U hE
  have h3 := fdiv_le_mul_div_S hW3L0 hOn hW3L hO
  have e : (w * hornR 4 1 (w ^ 4) 16 0 - w ^ 3 * hornR 4 3 (w ^ 4) 16 0) * S =
      w * S * (hornR 4 1 (w ^ 4) 16 0 * S) / S -
        w ^ 3 * S * (hornR 4 3 (w ^ 4) 16 0 * S) / S := by field_simp
  unfold atanSerU
  push_cast
  have h4 : Real.arctan w * S ≤
      (w * hornR 4 1 (w ^ 4) 16 0 - w ^ 3 * hornR 4 3 (w ^ 4) 16 0) * S + 1 := by
    have := mul_le_mul_of_nonneg_right (show Real.arctan w ≤
      (w * hornR 4 1 (w ^ 4) 16 0 - w ^ 3 * hornR 4 3 (w ^ 4) 16 0) + 1 / 2 ^ 64 by linarith)
      hS.le
    rw [add_mul, S_cast] at this
    rw [S_cast]
    norm_num at this ⊢
    linarith
  rw [e] at h4
  linarith

/-- For `w = N / D ∈ [0, 1/2]`, `atanSerL N D ≤ 2^64 arctan w`. -/
theorem atanSerL_le_arctan {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (h2 : 2 * N ≤ D) :
    (atanSerL N D : ℝ) ≤ Real.arctan (N / D) * S := by
  set w : ℝ := N / D with hw
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hw0 : 0 ≤ w := div_nonneg (by exact_mod_cast hN) hDr.le
  have hw2 : w ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ hDr]
    have : (2 * N : ℝ) ≤ D := by exact_mod_cast h2
    linarith
  have hS := S_real_pos
  have habs : |w| < 1 := (abs_of_nonneg hw0).trans_lt (by linarith)
  have hT := abs_arctan_sub_atanApprox_le habs (2 * 16)
  have hrem := atan_rem_le hw0 hw2
  rw [atanApprox_two_mul] at hT
  have hlo := (abs_le.1 (hT.trans hrem)).1
  have hV4U := pow_mul_S_le_cdiv (N := N) hD 4
  have hV4L := fdiv_le_pow_mul_S (N := N) hD 4
  have hW1L := fdiv_le_pow_mul_S (N := N) hD 1
  have hW3U := pow_mul_S_le_cdiv (N := N) hD 3
  simp only [pow_one] at hW1L
  rw [← hw] at hV4U hV4L hW1L hW3U
  have hN4 : 0 ≤ N ^ 4 * S := mul_nonneg (pow_nonneg hN 4) S_pos.le
  have hN1 : 0 ≤ N * S := mul_nonneg hN S_pos.le
  have hV4L0 := fdiv_nonneg hN4 (pow_pos hD 4)
  have hW1L0 := fdiv_nonneg hN1 hD
  have hE := hornL_le_hornR (a := 4) (b := 1) one_pos hV4L0 hV4L 16 0
  have hEn := hornL_nonneg (a := 4) (b := 1) hV4L0 16 0
  have hO := hornR_le_hornU (a := 4) (b := 3) (by norm_num)
    (by positivity : (0 : ℝ) ≤ w ^ 4) hV4U 16 0
  have hOr := hornR_nonneg 4 3 (by positivity : (0 : ℝ) ≤ w ^ 4) 16 0
  have h1 := fdiv_le_mul_div_S hW1L0 hEn hW1L hE
  have h3 := mul_div_S_le_cdiv (by positivity) (mul_nonneg hOr hS.le) hW3U hO
  have e : (w * hornR 4 1 (w ^ 4) 16 0 - w ^ 3 * hornR 4 3 (w ^ 4) 16 0) * S =
      w * S * (hornR 4 1 (w ^ 4) 16 0 * S) / S -
        w ^ 3 * S * (hornR 4 3 (w ^ 4) 16 0 * S) / S := by field_simp
  unfold atanSerL
  push_cast
  have h4 : (w * hornR 4 1 (w ^ 4) 16 0 - w ^ 3 * hornR 4 3 (w ^ 4) 16 0) * S - 1 ≤
      Real.arctan w * S := by
    have := mul_le_mul_of_nonneg_right (show
      (w * hornR 4 1 (w ^ 4) 16 0 - w ^ 3 * hornR 4 3 (w ^ 4) 16 0) - 1 / 2 ^ 64 ≤
        Real.arctan w by linarith) hS.le
    rw [sub_mul, S_cast] at this
    rw [S_cast]
    norm_num at this ⊢
    linarith
  rw [e] at h4
  linarith


/-- A lower bound for `2^64 arctan (1/2)`. -/
def arctanHalfLo : ℤ := 8552788783625223585
/-- An upper bound for `2^64 arctan (1/2)`. -/
def arctanHalfHi : ℤ := 8552788783625223589
/-- A lower bound for `2^64 π`. -/
def piLo : ℤ := 57952155664616982739
/-- An upper bound for `2^64 π`. -/
def piHi : ℤ := 57952155664616982740

/-- The value of `atanSerL 1 2` is `arctanHalfLo`. -/
theorem atanSerL_one_two : atanSerL 1 2 = arctanHalfLo := by decide +kernel
/-- The value of `atanSerU 1 2` is `arctanHalfHi`. -/
theorem atanSerU_one_two : atanSerU 1 2 = arctanHalfHi := by decide +kernel

/-- `arctanHalfLo ≤ 2^64 arctan (1/2)`. -/
theorem arctanHalfLo_le : (arctanHalfLo : ℝ) ≤ Real.arctan (1 / 2) * S := by
  have := atanSerL_le_arctan (N := 1) (D := 2) (by norm_num) (by norm_num) (by norm_num)
  rw [atanSerL_one_two] at this
  simpa using this

/-- `2^64 arctan (1/2) ≤ arctanHalfHi`. -/
theorem le_arctanHalfHi : Real.arctan (1 / 2) * S ≤ arctanHalfHi := by
  have := arctan_le_atanSerU (N := 1) (D := 2) (by norm_num) (by norm_num) (by norm_num)
  rw [atanSerU_one_two] at this
  simpa using this

/-- `piLo ≤ 2^64 π`. -/
theorem piLo_le : (piLo : ℝ) ≤ π * S := by
  have h := Real.pi_gt_d20
  rw [S_cast]
  have : (piLo : ℝ) ≤ 3.14159265358979323846 * 2 ^ 64 := by norm_num [piLo]
  nlinarith

/-- `2^64 π ≤ piHi`. -/
theorem le_piHi : π * S ≤ piHi := by
  have h := Real.pi_lt_d20
  rw [S_cast]
  have : 3.14159265358979323847 * 2 ^ 64 ≤ (piHi : ℝ) := by norm_num [piHi]
  nlinarith

/-- An upper bound for `2^64 arctan (N / D)` when `0 ≤ N ≤ D`, reducing to `[0, 1/2]` by
`arctan x = arctan (1/2) + arctan ((2x - 1)/(2 + x))`. -/
def atanCoreU (N D : ℤ) : ℤ :=
  if 2 * N ≤ D then atanSerU N D else arctanHalfHi + atanSerU (2 * N - D) (2 * D + N)

/-- A lower bound for `2^64 arctan (N / D)` when `0 ≤ N ≤ D`, as in
`Zeta5Irr.PotTableBound.atanCoreU`. -/
def atanCoreL (N D : ℤ) : ℤ :=
  if 2 * N ≤ D then atanSerL N D else arctanHalfLo + atanSerL (2 * N - D) (2 * D + N)

/-- For `1/2 < N/D ≤ 1`, `arctan (N/D) = arctan (1/2) + arctan ((2N - D)/(2D + N))`. -/
theorem arctan_eq_arctan_half_add {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) :
    Real.arctan (N / D) =
      Real.arctan (1 / 2) + Real.arctan (((2 * N - D : ℤ) : ℝ) / ((2 * D + N : ℤ) : ℝ)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hNr : (0 : ℝ) ≤ N := by exact_mod_cast hN
  have hE : (0 : ℝ) < 2 * D + N := by linarith
  have hD0 : (D : ℝ) ≠ 0 := hDr.ne'
  push_cast
  rw [Real.arctan_add]
  · congr 1
    field_simp
    ring_nf
    rw [mul_comm (D : ℝ), mul_assoc, mul_inv_cancel₀ hD0, mul_one]
  · rw [← mul_div_assoc, div_lt_one hE]
    linarith

/-- For `0 ≤ N ≤ D` with `D > 0`, `2^64 arctan (N / D) ≤ atanCoreU N D`. -/
theorem arctan_le_atanCoreU {N D : ℤ} (hN : 0 ≤ N) (hND : N ≤ D) (hD : 0 < D) :
    Real.arctan (N / D) * S ≤ atanCoreU N D := by
  unfold atanCoreU
  split_ifs with h
  · exact arctan_le_atanSerU hN hD h
  · rw [arctan_eq_arctan_half_add hN hD, add_mul]
    have := arctan_le_atanSerU (N := 2 * N - D) (D := 2 * D + N) (by omega) (by omega)
      (by omega)
    push_cast at this ⊢
    linarith [le_arctanHalfHi]

/-- For `0 ≤ N ≤ D` with `D > 0`, `atanCoreL N D ≤ 2^64 arctan (N / D)`. -/
theorem atanCoreL_le_arctan {N D : ℤ} (hN : 0 ≤ N) (hND : N ≤ D) (hD : 0 < D) :
    (atanCoreL N D : ℝ) ≤ Real.arctan (N / D) * S := by
  unfold atanCoreL
  split_ifs with h
  · exact atanSerL_le_arctan hN hD h
  · rw [arctan_eq_arctan_half_add hN hD, add_mul]
    have := atanSerL_le_arctan (N := 2 * N - D) (D := 2 * D + N) (by omega) (by omega)
      (by omega)
    push_cast at this ⊢
    linarith [arctanHalfLo_le]

/-- An upper bound for `2^64 arctan (X / 2^64)` when `X ≥ 0`, using
`arctan x = π/2 - arctan (1/x)` above `1`. -/
def atanU (X : ℤ) : ℤ := if X ≤ S then atanCoreU X S else cdiv piHi 2 - atanCoreL S X

/-- A lower bound for `2^64 arctan (X / 2^64)` when `X ≥ 0`. -/
def atanL (X : ℤ) : ℤ := if X ≤ S then atanCoreL X S else fdiv piLo 2 - atanCoreU S X

/-- For `X > 2^64`, `arctan (X / 2^64) = π/2 - arctan (2^64 / X)`. -/
theorem arctan_div_S_of_lt {X : ℤ} (h : S < X) :
    Real.arctan (X / S) = π / 2 - Real.arctan (S / X) := by
  have hX : (0 : ℝ) < X := S_real_pos.trans (by exact_mod_cast h)
  rw [← Real.arctan_inv_of_pos (div_pos S_real_pos hX), inv_div]

/-- For `X ≥ 0`, `2^64 arctan (X / 2^64) ≤ atanU X`. -/
theorem arctan_le_atanU {X : ℤ} (hX : 0 ≤ X) : Real.arctan (X / S) * S ≤ atanU X := by
  unfold atanU
  split_ifs with h
  · exact arctan_le_atanCoreU hX h S_pos
  · have hlt : S < X := not_le.1 h
    rw [arctan_div_S_of_lt hlt, sub_mul]
    have h1 := atanCoreL_le_arctan S_pos.le hlt.le (S_pos.trans hlt)
    have h2 := le_cdiv piHi (by norm_num : (0 : ℤ) < 2)
    push_cast at h1 h2 ⊢
    have := le_piHi
    have e : π / 2 * S = π * S / 2 := by ring
    linarith

/-- For `X ≥ 0`, `atanL X ≤ 2^64 arctan (X / 2^64)`. -/
theorem atanL_le_arctan {X : ℤ} (hX : 0 ≤ X) : (atanL X : ℝ) ≤ Real.arctan (X / S) * S := by
  unfold atanL
  split_ifs with h
  · exact atanCoreL_le_arctan hX h S_pos
  · have hlt : S < X := not_le.1 h
    rw [arctan_div_S_of_lt hlt, sub_mul]
    have h1 := arctan_le_atanCoreU S_pos.le hlt.le (S_pos.trans hlt)
    have h2 := fdiv_le piLo (by norm_num : (0 : ℤ) < 2)
    push_cast at h1 h2 ⊢
    have := piLo_le
    have e : π / 2 * S = π * S / 2 := by ring
    linarith


/-! ### Square roots -/

/-- At most `n` steps of Newton's iteration `g ↦ (g + M / g) / 2` for `√M`, stopped when it
no longer decreases. -/
def newton (M : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | n + 1, g => let g' := (g + M / g) / 2; if g' < g then newton M n g' else g

/-- An approximate integer square root, by Newton's iteration from a power of two. -/
def isqrt (M : ℕ) : ℕ := if M = 0 then 0 else newton M 20 (2 ^ (lg2 M / 2 + 1))

/-- A natural number at most `√M`. -/
def isqrtLo (M : ℕ) : ℕ := let n := isqrt M; if n * n ≤ M then n else 0

/-- A natural number at least `√M`. -/
def isqrtHi (M : ℕ) : ℕ := let n := isqrt M + 1; if M ≤ n * n then n else M

/-- `isqrtLo M ≤ √M`. -/
theorem isqrtLo_le (M : ℕ) : (isqrtLo M : ℝ) ≤ √(M : ℝ) := by
  unfold isqrtLo
  simp only
  split_ifs with h
  · have h' : ((isqrt M : ℝ)) * isqrt M ≤ M := by exact_mod_cast h
    rw [← Real.sqrt_mul_self (Nat.cast_nonneg (isqrt M))]
    exact Real.sqrt_le_sqrt h'
  · simp

/-- `√M ≤ isqrtHi M`. -/
theorem sqrt_le_isqrtHi (M : ℕ) : √(M : ℝ) ≤ isqrtHi M := by
  unfold isqrtHi
  simp only
  split_ifs with h
  · have h' : (M : ℝ) ≤ ((isqrt M + 1 : ℕ) : ℝ) * ((isqrt M + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [← Real.sqrt_mul_self (Nat.cast_nonneg (isqrt M + 1))]
    exact Real.sqrt_le_sqrt h'
  · have h' : (M : ℝ) ≤ (M : ℝ) * M := by exact_mod_cast Nat.le_mul_self M
    calc √(M : ℝ) ≤ √((M : ℝ) * M) := Real.sqrt_le_sqrt h'
      _ = M := Real.sqrt_mul_self (Nat.cast_nonneg M)

/-- A lower bound for `2^64 √(X / Q)`. -/
def sqL (X Q : ℤ) : ℤ := isqrtLo (fdiv (X * S * S) Q).toNat

/-- An upper bound for `2^64 √(X / Q)`. -/
def sqU (X Q : ℤ) : ℤ := isqrtHi (cdiv (X * S * S) Q).toNat

/-- For `X ≥ 0` and `Q > 0`, `2^64 √(X / Q) = √(2^128 X / Q)`. -/
theorem sqrt_mul_S {X Q : ℤ} (hX : 0 ≤ X) (hQ : 0 < Q) :
    √((X : ℝ) / Q) * S = √((X * S * S : ℤ) / (Q : ℝ)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  push_cast
  rw [show (X : ℝ) * S * S / Q = X / Q * (S * S) by ring,
    Real.sqrt_mul (div_nonneg (by exact_mod_cast hX) hQr.le),
    Real.sqrt_mul_self S_real_pos.le]

/-- For `X ≥ 0` and `Q > 0`, `sqL X Q ≤ 2^64 √(X / Q)`. -/
theorem sqL_le {X Q : ℤ} (hX : 0 ≤ X) (hQ : 0 < Q) : (sqL X Q : ℝ) ≤ √((X : ℝ) / Q) * S := by
  have hM : 0 ≤ fdiv (X * S * S) Q := fdiv_nonneg (by have := S_pos; positivity) hQ
  have h1 := isqrtLo_le (fdiv (X * S * S) Q).toNat
  have h2 := fdiv_le (X * S * S) hQ
  push_cast at h2
  have e : (((fdiv (X * S * S) Q).toNat : ℕ) : ℝ) = (fdiv (X * S * S) Q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hM
  rw [e] at h1
  rw [sqrt_mul_S hX hQ]
  unfold sqL
  push_cast
  exact h1.trans (Real.sqrt_le_sqrt h2)

/-- For `X ≥ 0` and `Q > 0`, `2^64 √(X / Q) ≤ sqU X Q`. -/
theorem le_sqU {X Q : ℤ} (hX : 0 ≤ X) (hQ : 0 < Q) : √((X : ℝ) / Q) * S ≤ sqU X Q := by
  have hM : 0 ≤ cdiv (X * S * S) Q := cdiv_nonneg (by have := S_pos; positivity) hQ
  have h1 := sqrt_le_isqrtHi (cdiv (X * S * S) Q).toNat
  have h2 := le_cdiv (X * S * S) hQ
  push_cast at h2
  have e : (((cdiv (X * S * S) Q).toNat : ℕ) : ℝ) = (cdiv (X * S * S) Q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hM
  rw [e] at h1
  rw [sqrt_mul_S hX hQ]
  unfold sqU
  push_cast
  exact (Real.sqrt_le_sqrt h2).trans h1

/-! ### The external field -/

/-- The closed form of the external field, with its four occurrences of the variable
separated: `Φ(t₁, t₂, t₃, t₄) = log (1 + t₁) - 6 α log (t₂ + α²) - 2 + 12 α
  + 2 √t₃ (π + arctan (1 / √t₃) - 6 arctan (α / √t₄))`. -/
noncomputable def fieldForm (t₁ t₂ t₃ t₄ : ℝ) : ℝ :=
  Real.log (1 + t₁) - 6 * (innerRatio : ℝ) * Real.log (t₂ + (innerRatio : ℝ) ^ 2) - 2 +
    12 * (innerRatio : ℝ) +
    2 * √t₃ * (π + Real.arctan (1 / √t₃) - 6 * Real.arctan ((innerRatio : ℝ) / √t₄))

/-- A lower bound for `2^64 Φ(X₁/Q, X₂/Q, X₃/Q, X₄/Q)`, or `none` if one of its side
conditions fails. -/
def phiL (X₁ X₂ X₃ X₄ Q : ℤ) : Option ℤ :=
  if 0 < Q ∧ 0 ≤ X₁ ∧ 0 ≤ X₂ ∧ 0 ≤ X₃ ∧ 0 ≤ X₄ ∧ 0 < sqL X₃ Q ∧ 0 < sqL X₄ Q ∧
      0 < fdiv ((Q + X₁) * S) Q then
    let PL := piLo + atanL (fdiv (S * S) (sqU X₃ Q)) -
      6 * atanU (cdiv (3 * S * S) (40 * sqL X₄ Q))
    let spL := if 0 ≤ PL then fdiv (sqL X₃ Q * PL) S else fdiv (sqU X₃ Q * PL) S
    some (logL (fdiv ((Q + X₁) * S) Q) -
      cdiv (9 * logU (cdiv ((1600 * X₂ + 9 * Q) * S) (1600 * Q))) 20 +
      fdiv (-11 * S) 10 + 2 * spL)
  else none

/-- If `phiL X₁ X₂ X₃ X₄ Q = some w`, then `w ≤ 2^64 Φ(X₁/Q, X₂/Q, X₃/Q, X₄/Q)`. -/
theorem le_fieldForm_of_phiL {X₁ X₂ X₃ X₄ Q w : ℤ} (h : phiL X₁ X₂ X₃ X₄ Q = some w) :
    (w : ℝ) ≤ fieldForm (X₁ / Q) (X₂ / Q) (X₃ / Q) (X₄ / Q) * S := by
  unfold phiL at h
  split_ifs at h with hc
  obtain ⟨hQ, hX1, hX2, hX3, hX4, hs3, hs4, hY1⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  have hS := S_real_pos
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  set t₁ : ℝ := X₁ / Q
  set t₂ : ℝ := X₂ / Q
  set t₃ : ℝ := X₃ / Q
  set t₄ : ℝ := X₄ / Q
  have ht₁ : 0 ≤ t₁ := div_nonneg (by exact_mod_cast hX1) hQr.le
  have ht₂ : 0 ≤ t₂ := div_nonneg (by exact_mod_cast hX2) hQr.le
  have h3L := sqL_le hX3 hQ
  have h3U := le_sqU hX3 hQ
  have h4L := sqL_le hX4 hQ
  have hs3r : (0 : ℝ) < sqL X₃ Q := by exact_mod_cast hs3
  have hs4r : (0 : ℝ) < sqL X₄ Q := by exact_mod_cast hs4
  have hr3 : 0 < √t₃ := by
    by_contra! hn
    nlinarith
  have hr4 : 0 < √t₄ := by
    by_contra! hn
    nlinarith
  have hsU : (0 : ℝ) < sqU X₃ Q := by nlinarith
  have hsU' : 0 < sqU X₃ Q := by exact_mod_cast hsU
  set I := fdiv (S * S) (sqU X₃ Q)
  have hI0 : 0 ≤ I := fdiv_nonneg (mul_pos S_pos S_pos).le hsU'
  have hI : (I : ℝ) / S ≤ 1 / √t₃ := by
    have h1 := fdiv_le (S * S) hsU'
    push_cast at h1
    rw [div_le_iff₀ hS]
    calc (I : ℝ) ≤ S * S / sqU X₃ Q := h1
      _ ≤ S * S / (√t₃ * S) := by gcongr
      _ = 1 / √t₃ * S := by field_simp
  have hA1 : (atanL I : ℝ) ≤ Real.arctan (1 / √t₃) * S :=
    (atanL_le_arctan hI0).trans (mul_le_mul_of_nonneg_right
      (Real.arctan_strictMono.monotone hI) hS.le)
  set J := cdiv (3 * S * S) (40 * sqL X₄ Q)
  have hJ0 : 0 ≤ J := cdiv_nonneg (by have := S_pos; positivity) (by omega)
  have hJ : (innerRatio : ℝ) / √t₄ ≤ J / S := by
    have h1 := le_cdiv (3 * S * S) (by omega : 0 < 40 * sqL X₄ Q)
    push_cast at h1
    rw [le_div_iff₀ hS]
    calc (innerRatio : ℝ) / √t₄ * S = 3 * S * S / (40 * (√t₄ * S)) := by
          rw [innerRatio]; push_cast; field_simp
      _ ≤ 3 * S * S / (40 * sqL X₄ Q) := by gcongr
      _ ≤ J := h1
  have hA2 : Real.arctan ((innerRatio : ℝ) / √t₄) * S ≤ atanU J :=
    (mul_le_mul_of_nonneg_right (Real.arctan_strictMono.monotone hJ) hS.le).trans
      (arctan_le_atanU hJ0)
  set p := π + Real.arctan (1 / √t₃) - 6 * Real.arctan ((innerRatio : ℝ) / √t₄)
  set PL := piLo + atanL I - 6 * atanU J
  have hPL : (PL : ℝ) ≤ p * S := by
    have := piLo_le
    simp only [PL, p]
    push_cast
    linarith
  have hsp : ((if 0 ≤ PL then fdiv (sqL X₃ Q * PL) S else fdiv (sqU X₃ Q * PL) S : ℤ) : ℝ) ≤
      √t₃ * p * S := by
    have e : √t₃ * p * S = √t₃ * S * (p * S) / S := by field_simp
    rw [e]
    split_ifs with hp
    · exact fdiv_le_mul_div_S hs3.le hp h3L hPL
    · have h1 := fdiv_le (sqU X₃ Q * PL) S_pos
      push_cast at h1
      refine h1.trans (div_le_div_of_nonneg_right ?_ hS.le)
      have hp' : (PL : ℝ) < 0 := by exact_mod_cast not_le.1 hp
      calc (sqU X₃ Q : ℝ) * PL ≤ √t₃ * S * PL := mul_le_mul_of_nonpos_right h3U hp'.le
        _ ≤ √t₃ * S * (p * S) := mul_le_mul_of_nonneg_left hPL (by positivity)
  have hL1 : (logL (fdiv ((Q + X₁) * S) Q) : ℝ) ≤ Real.log (1 + t₁) * S := by
    refine logL_le_log_mul_S hY1 ?_
    have h1 := fdiv_le ((Q + X₁) * S) hQ
    push_cast at h1
    calc _ ≤ _ := h1
      _ = (1 + t₁) * S := by simp only [t₁]; field_simp
  have hL2 : Real.log (t₂ + (innerRatio : ℝ) ^ 2) * S ≤
      logU (cdiv ((1600 * X₂ + 9 * Q) * S) (1600 * Q)) := by
    refine log_mul_S_le_logU (by rw [innerRatio]; positivity) ?_
    have h1 := le_cdiv ((1600 * X₂ + 9 * Q) * S) (by omega : 0 < 1600 * Q)
    push_cast at h1
    calc (t₂ + (innerRatio : ℝ) ^ 2) * S = (1600 * X₂ + 9 * Q) * S / (1600 * Q) := by
          simp only [t₂, innerRatio]; push_cast; field_simp; ring
      _ ≤ _ := h1
  have hc9 := le_cdiv (9 * logU (cdiv ((1600 * X₂ + 9 * Q) * S) (1600 * Q)))
    (by norm_num : (0 : ℤ) < 20)
  have hc11 := fdiv_le (-11 * S) (by norm_num : (0 : ℤ) < 10)
  push_cast at hc9 hc11 hsp ⊢
  unfold fieldForm
  have hα : (innerRatio : ℝ) = 3 / 40 := by rw [innerRatio]; push_cast; ring
  rw [hα] at hL2 ⊢
  simp only [p] at hsp
  rw [hα] at hsp
  nlinarith


/-! ### The potential of `ρ` -/

open MeasureTheory

/-- The sixteen upper bounds for `log ((bᵢ - aᵢ) / 4) · 2^64`. -/
def insideU : List ℤ :=
  [-122994926142567314013, -105642496625772332999, -94123147396641908395, -84482370197881159167,
   -75917073953075162745, -68217433244526318277, -61315981028116654459, -55179274081414559197,
   -49781601018869450287, -45099542035719462321, -41111318357483477395, -37796994411480563581,
   -35138804315152349455, -33121543423155273213, -31732988316899833821, -30964081311736571347]

/-- `logU` applied to `⌈2^64 (bᵢ - aᵢ) / 4⌉` is the `i`-th entry of `insideU`. -/
theorem logU_inside (i : Fin 16) :
    logU (cdiv ((rhoBNum i - rhoANum i : ℤ) * S) (4 * 10 ^ 12)) = insideU.getD i 0 := by
  revert i
  decide +kernel

/-- An upper bound for `2^64 U^{ω_{[aᵢ,bᵢ]}}(X / (10¹² 2^d))`. -/
def termU (i : Fin 16) (X : ℤ) (d : ℕ) : ℤ :=
  if rhoANum i * 2 ^ d ≤ X ∧ X ≤ rhoBNum i * 2 ^ d then insideU.getD i 0
  else logU (cdiv ((|2 * X - rhoANum i * 2 ^ d - rhoBNum i * 2 ^ d| +
      2 * isqrtHi ((X - rhoANum i * 2 ^ d) * (X - rhoBNum i * 2 ^ d)).toNat) * S)
    (4 * (10 ^ 12 * 2 ^ d)))

/-- `2^64 U^{ω_{[aᵢ,bᵢ]}}(X / (10¹² 2^d)) ≤ termU i X d`. -/
theorem logPotential_le_termU (i : Fin 16) (X : ℤ) (d : ℕ) :
    logPotential ((arcsineMeasure (rhoA i) (rhoB i)).map ((↑) : ℝ → ℂ))
      (((X : ℝ) / (10 ^ 12 * 2 ^ d) : ℝ) : ℂ) * S ≤ termU i X d := by
  set Q : ℝ := 10 ^ 12 * 2 ^ d with hQ
  have hQ0 : 0 < Q := by positivity
  set A : ℤ := rhoANum i * 2 ^ d with hA
  set B : ℤ := rhoBNum i * 2 ^ d with hB
  have ha : (rhoA i : ℝ) = A / Q := by
    rw [rhoA, hA, hQ]; push_cast; field_simp
  have hb : (rhoB i : ℝ) = B / Q := by
    rw [rhoB, hB, hQ]; push_cast; field_simp
  have hab := rhoA_lt_rhoB_real i
  have hAB : A < B := by
    rw [ha, hb] at hab
    exact_mod_cast (div_lt_div_iff_of_pos_right hQ0).1 hab
  unfold termU
  split_ifs with h
  · have hx : (X : ℝ) / Q ∈ Set.Icc (rhoA i : ℝ) (rhoB i) := by
      rw [ha, hb]
      exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast h.1) hQ0.le,
        div_le_div_of_nonneg_right (by exact_mod_cast h.2) hQ0.le⟩
    rw [logPotential_arcsineMeasure hab hx, ← logU_inside]
    refine log_mul_S_le_logU (by linarith) ?_
    have := le_cdiv ((rhoBNum i - rhoANum i : ℤ) * S) (by norm_num : (0 : ℤ) < 4 * 10 ^ 12)
    push_cast at this ⊢
    refine le_trans (le_of_eq ?_) this
    rw [rhoA, rhoB]; push_cast; ring
  · have hout : X < A ∨ B < X := by
      by_contra hn
      push Not at hn
      exact h ⟨hn.1, hn.2⟩
    have hout' : (X : ℝ) / Q < rhoA i ∨ (rhoB i : ℝ) < X / Q := by
      rw [ha, hb]
      rcases hout with ho | ho
      · exact Or.inl (div_lt_div_of_pos_right (by exact_mod_cast ho) hQ0)
      · exact Or.inr (div_lt_div_of_pos_right (by exact_mod_cast ho) hQ0)
    rw [logPotential_arcsineMeasure_of_notMem hab hout']
    have hP : 0 ≤ (X - A) * (X - B) := by rcases hout with ho | ho <;> nlinarith
    set M := ((X - A) * (X - B)).toNat
    have hM : (M : ℝ) = ((X - A) * (X - B) : ℤ) := by exact_mod_cast Int.toNat_of_nonneg hP
    have hsq := sqrt_le_isqrtHi M
    rw [hM] at hsq
    have hc : 0 < |(X : ℝ) / Q - (rhoA i + rhoB i) / 2| := by
      rw [abs_pos, sub_ne_zero]
      rintro h'
      rcases hout' with ho | ho <;> linarith
    refine log_mul_S_le_logU (by positivity) ?_
    have h1 := le_cdiv ((|2 * X - A - B| + 2 * (isqrtHi M : ℤ)) * S)
      (by positivity : (0 : ℤ) < 4 * (10 ^ 12 * 2 ^ d))
    push_cast at h1 hsq ⊢
    refine le_trans ?_ h1
    have e1 : |(X : ℝ) / Q - (rhoA i + rhoB i) / 2| = |2 * (X : ℝ) - A - B| / (2 * Q) := by
      rw [ha, hb, show (X : ℝ) / Q - (A / Q + B / Q) / 2 = (2 * X - A - B) / (2 * Q) by
        field_simp; ring, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Q)]
    have e2 : √(((X : ℝ) / Q - rhoA i) * (X / Q - rhoB i)) =
        √(((X : ℝ) - A) * (X - B)) / Q := by
      rw [ha, hb, show ((X : ℝ) / Q - A / Q) * (X / Q - B / Q) = ((X - A) * (X - B)) / (Q * Q) by
        field_simp, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hQ0.le]
    rw [e1, e2]
    have hS := S_real_pos
    rw [show (4 : ℝ) * (1000000000000 * 2 ^ d) = 4 * Q by rw [hQ]; norm_num]
    rw [le_div_iff₀ (by positivity)]
    have : (|2 * (X : ℝ) - A - B| / (2 * Q) + √(((X : ℝ) - A) * (X - B)) / Q) / 2 * S * (4 * Q)
        = (|2 * (X : ℝ) - A - B| + 2 * √(((X : ℝ) - A) * (X - B))) * S := by
      field_simp; ring
    rw [this]
    gcongr

/-- An upper bound for `10¹² 2^64 U^ρ(X / (10¹² 2^d))`. -/
def uU (X : ℤ) (d : ℕ) : ℤ := ∑ i : Fin 16, (rhoCNum i : ℤ) * termU i X d

/-- `10¹² 2^64 U^ρ(X / (10¹² 2^d)) ≤ uU X d`. -/
theorem logPotential_rho_le_uU (X : ℤ) (d : ℕ) :
    logPotential (rho.map ((↑) : ℝ → ℂ)) (((X : ℝ) / (10 ^ 12 * 2 ^ d) : ℝ) : ℂ) *
      (10 ^ 12 * S) ≤
      uU X d := by
  rw [logPotential_rho_eq_sum, Finset.sum_mul, uU, Int.cast_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Int.cast_mul, Int.cast_natCast]
  have h := logPotential_le_termU i X d
  rw [rhoC_eq, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  calc (rhoCNum i : ℝ) / 10 ^ 12 * logPotential ((arcsineMeasure (rhoA i) (rhoB i)).map
        ((↑) : ℝ → ℂ)) (((X : ℝ) / (10 ^ 12 * 2 ^ d) : ℝ) : ℂ) * (10 ^ 12 * S)
      = rhoCNum i * (logPotential ((arcsineMeasure (rhoA i) (rhoB i)).map
        ((↑) : ℝ → ℂ)) (((X : ℝ) / (10 ^ 12 * 2 ^ d) : ℝ) : ℂ) * S) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)


/-! ### The field terms of the interval bound -/

/-- For `t > 0`, the external field is `V(t) = Φ(t, t, t, t)`. -/
theorem externalField_eq_fieldForm {t : ℝ} (ht : 0 < t) :
    externalField t = fieldForm t t t t := by
  rw [externalField_eq ht, fieldForm]

/-- The constant `V_*` is `Φ(q₋, q₊, q₊, q₋)` with `q₋ = 5920507700 / 10¹²` and
`q₊ = 5920507900 / 10¹²`. -/
theorem externalFieldFloor_eq_fieldForm :
    externalFieldFloor =
      fieldForm ((5920507700 : ℤ) / ((10 ^ 12 : ℤ) : ℝ)) ((5920507900 : ℤ) / ((10 ^ 12 : ℤ) : ℝ))
        ((5920507900 : ℤ) / ((10 ^ 12 : ℤ) : ℝ)) ((5920507700 : ℤ) / ((10 ^ 12 : ℤ) : ℝ)) := by
  have h1 : ((externalFieldMinLower : ℚ) : ℝ) = (5920507700 : ℤ) / ((10 ^ 12 : ℤ) : ℝ) := by
    rw [externalFieldMinLower]; push_cast; norm_num
  have h2 : ((externalFieldMinUpper : ℚ) : ℝ) = (5920507900 : ℤ) / ((10 ^ 12 : ℤ) : ℝ) := by
    rw [externalFieldMinUpper]; push_cast; norm_num
  rw [externalFieldFloor, fieldForm, ← h1, ← h2, one_div]

/-- If `phiL X₁ X₂ X₃ X₄ Q = some w`, then `X₃ / Q > 0`. -/
theorem pos_of_phiL {X₁ X₂ X₃ X₄ Q w : ℤ} (h : phiL X₁ X₂ X₃ X₄ Q = some w) :
    0 < (X₃ : ℝ) / Q := by
  unfold phiL at h
  split_ifs at h with hc
  obtain ⟨hQ, -, -, hX3, -, hs3, -⟩ := hc
  have h3 := sqL_le hX3 hQ
  have hs : (0 : ℝ) < sqL X₃ Q := by exact_mod_cast hs3
  have : 0 < √((X₃ : ℝ) / Q) := by
    by_contra hn
    have hn := not_lt.1 hn
    nlinarith [S_real_pos]
  exact Real.sqrt_pos.1 this

/-! ### The grid and the cells -/

/-- The grid points `Aⱼ`, multiplied by `10¹²`. -/
def gridNum : List ℤ :=
  [0, 71741310, 74129565, 78667711, 85815639, 96349355, 111522114, 133347132, 165097686,
   212206188, 283911191, 396324613, 578197906, 881725356, 1402286665, 2312248264, 3906748086,
   5920507700, 5920507900,
   8992695531, 15340997855, 25730180724, 41909578246, 65851089563, 99481037884,
   144325727458, 201105762729, 269345996903, 347089554156, 430806704415, 515561896511,
   595448778546, 664241383483, 716160577112, 746637295669, 2000000000000]

/-- `10¹² Aᵢ` is the `i`-th entry of `gridNum`. -/
theorem potGrid_mul (i : Fin 36) : potGrid i * 10 ^ 12 = gridNum.getD i 0 := by
  revert i
  decide +kernel

/-- The grid point `Aᵢ` is the `i`-th entry of `gridNum` divided by `10¹²`. -/
theorem potGrid_cast (i : Fin 36) : (potGrid i : ℝ) = (gridNum.getD i 0 : ℝ) / 10 ^ 12 := by
  have h : ((potGrid i * 10 ^ 12 : ℚ) : ℝ) = ((gridNum.getD i 0 : ℤ) : ℝ) := by
    rw [potGrid_mul]; push_cast; rfl
  push_cast at h
  rw [eq_div_iff (by norm_num), h]

/-- The numerator of the left end of `J_{j,d,k}` over the denominator `10¹² 2^d`:
`10¹² (2^d Aⱼ + (Aⱼ₊₁ - Aⱼ) k)`. -/
def xL (j d k : ℕ) : ℤ :=
  gridNum.getD j 0 * 2 ^ d + (gridNum.getD (j + 1) 0 - gridNum.getD j 0) * k

/-- The left end of `J_{j,d,k}` is `xL j d k / (10¹² 2^d)`. -/
theorem potIntervalLeft_eq (j : ℕ) (hj : j < 35) (d k : ℕ) :
    potIntervalLeft ⟨j, hj⟩ d k = (xL j d k : ℝ) / ((10 ^ 12 * 2 ^ d : ℤ) : ℝ) := by
  rw [potIntervalLeft, potGrid_cast, potGrid_cast, xL]
  simp only [Fin.val_castSucc, Fin.val_succ]
  push_cast
  field_simp
  ring

/-- The right end of `J_{j,d,k}` is `xL j d (k + 1) / (10¹² 2^d)`. -/
theorem potIntervalRight_eq (j : ℕ) (hj : j < 35) (d k : ℕ) :
    potIntervalRight ⟨j, hj⟩ d k = (xL j d (k + 1) : ℝ) / ((10 ^ 12 * 2 ^ d : ℤ) : ℝ) := by
  rw [potIntervalRight_eq_potIntervalLeft_succ, potIntervalLeft_eq]

/-- The lower bound for the field term of `𝓑` on the cell `J_{j,d,k}`. -/
def cellField (j d k : ℕ) : Option ℤ :=
  if xL j d (k + 1) ≤ 5920507700 * 2 ^ d then
    phiL (xL j d (k + 1)) (xL j d (k + 1)) (xL j d (k + 1)) (xL j d (k + 1)) (10 ^ 12 * 2 ^ d)
  else if 5920507900 * 2 ^ d ≤ xL j d k then
    phiL (xL j d k) (xL j d k) (xL j d k) (xL j d k) (10 ^ 12 * 2 ^ d)
  else phiL 5920507700 5920507900 5920507900 5920507700 (10 ^ 12)

/-- If `cellField j d k = some w` and the ends `l ≤ r` of `J_{j,d,k}` are ordered, then
`𝓑(l, r) ≤ 2 max (U^ρ(l), U^ρ(r)) - w / 2^64`. -/
theorem potBound_le_of_cellField {j d k : ℕ} (hj : j < 35) {w : ℤ}
    (hw : cellField j d k = some w) (hlr : xL j d k ≤ xL j d (k + 1)) :
    potBound (potIntervalLeft ⟨j, hj⟩ d k) (potIntervalRight ⟨j, hj⟩ d k) ≤
      2 * max (logPotential (rho.map ((↑) : ℝ → ℂ)) (potIntervalLeft ⟨j, hj⟩ d k))
        (logPotential (rho.map ((↑) : ℝ → ℂ)) (potIntervalRight ⟨j, hj⟩ d k)) - w / S := by
  have hS := S_real_pos
  have hQ : (0 : ℝ) < ((10 ^ 12 * 2 ^ d : ℤ) : ℝ) := by positivity
  have hqm : ((externalFieldMinLower : ℚ) : ℝ) = (5920507700 * 2 ^ d : ℤ) /
      ((10 ^ 12 * 2 ^ d : ℤ) : ℝ) := by
    rw [externalFieldMinLower]; push_cast; field_simp; norm_num
  have hqp : ((externalFieldMinUpper : ℚ) : ℝ) = (5920507900 * 2 ^ d : ℤ) /
      ((10 ^ 12 * 2 ^ d : ℤ) : ℝ) := by
    rw [externalFieldMinUpper]; push_cast; field_simp; norm_num
  have hl := potIntervalLeft_eq j hj d k
  have hr := potIntervalRight_eq j hj d k
  unfold cellField at hw
  split_ifs at hw with h1 h2
  · have hrq : potIntervalRight ⟨j, hj⟩ d k ≤ (externalFieldMinLower : ℝ) := by
      rw [hr, hqm]; exact div_le_div_of_nonneg_right (by exact_mod_cast h1) hQ.le
    rw [potBound_of_le_minLower hrq]
    have hv := le_fieldForm_of_phiL hw
    rw [← hr, ← externalField_eq_fieldForm (by rw [hr]; exact pos_of_phiL hw)] at hv
    have : (w : ℝ) / S ≤ externalField (potIntervalRight ⟨j, hj⟩ d k) := by
      rw [div_le_iff₀ hS]; exact hv
    linarith
  · have hlq : (externalFieldMinUpper : ℝ) ≤ potIntervalLeft ⟨j, hj⟩ d k := by
      rw [hl, hqp]; exact div_le_div_of_nonneg_right (by exact_mod_cast h2) hQ.le
    have hlr' : potIntervalLeft ⟨j, hj⟩ d k ≤ potIntervalRight ⟨j, hj⟩ d k := by
      rw [hl, hr]; exact div_le_div_of_nonneg_right (by exact_mod_cast hlr) hQ.le
    rw [potBound_of_minUpper_le hlr' hlq]
    have hv := le_fieldForm_of_phiL hw
    rw [← hl, ← externalField_eq_fieldForm (by rw [hl]; exact pos_of_phiL hw)] at hv
    have : (w : ℝ) / S ≤ externalField (potIntervalLeft ⟨j, hj⟩ d k) := by
      rw [div_le_iff₀ hS]; exact hv
    linarith
  · have hrq : (externalFieldMinLower : ℝ) < potIntervalRight ⟨j, hj⟩ d k := by
      rw [hr, hqm]; exact div_lt_div_of_pos_right (by exact_mod_cast not_le.1 h1) hQ
    have hlq : potIntervalLeft ⟨j, hj⟩ d k < (externalFieldMinUpper : ℝ) := by
      rw [hl, hqp]; exact div_lt_div_of_pos_right (by exact_mod_cast not_le.1 h2) hQ
    rw [potBound_of_mem hrq hlq]
    have hv := le_fieldForm_of_phiL hw
    rw [← externalFieldFloor_eq_fieldForm] at hv
    have : (w : ℝ) / S ≤ externalFieldFloor := by
      rw [div_le_iff₀ hS]; exact hv
    linarith

/-- The check that the certified upper bound for `𝓑` on the cell `J_{j,d,k}` is below
`-6645002 / 10⁶`, given upper bounds `uL`, `uR` for `10¹² 2^64 U^ρ` at its two ends. -/
def cellCheck (j d k : ℕ) (uL uR : ℤ) : Bool :=
  match cellField j d k with
  | some w => decide (xL j d k ≤ xL j d (k + 1)) &&
      decide (2 * max uL uR - w * 10 ^ 12 < -6645002 * 10 ^ 6 * S)
  | none => false

/-- If `cellCheck` succeeds on `J_{j,d,k} = [l, r]` with the bounds `uU` at its ends, then
`𝓑(l, r) < -6645002 / 10⁶`. -/
theorem potBound_lt_of_cellCheck {j d k : ℕ} (hj : j < 35)
    (h : cellCheck j d k (uU (xL j d k) d) (uU (xL j d (k + 1)) d) = true) :
    potBound (potIntervalLeft ⟨j, hj⟩ d k) (potIntervalRight ⟨j, hj⟩ d k) <
      -6645002 / 10 ^ 6 := by
  unfold cellCheck at h
  rcases hw : cellField j d k with _ | w
  · simp [hw] at h
  simp only [hw, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlr, hlt⟩ := h
  have hB := potBound_le_of_cellField hj hw hlr
  have hS := S_real_pos
  have hQ : ((10 ^ 12 * 2 ^ d : ℤ) : ℝ) = 10 ^ 12 * 2 ^ d := by push_cast; ring
  have hUl := logPotential_rho_le_uU (xL j d k) d
  have hUr := logPotential_rho_le_uU (xL j d (k + 1)) d
  rw [← hQ, ← potIntervalLeft_eq j hj] at hUl
  rw [← hQ, ← potIntervalRight_eq j hj] at hUr
  set Ul := logPotential (rho.map ((↑) : ℝ → ℂ)) (potIntervalLeft ⟨j, hj⟩ d k)
  set Ur := logPotential (rho.map ((↑) : ℝ → ℂ)) (potIntervalRight ⟨j, hj⟩ d k)
  have hmax : max Ul Ur * (10 ^ 12 * S) ≤ max (uU (xL j d k) d : ℝ) (uU (xL j d (k + 1)) d) := by
    rw [max_mul_of_nonneg _ _ (by positivity)]
    exact max_le_max hUl hUr
  have hlt' : (2 * max (uU (xL j d k) d : ℝ) (uU (xL j d (k + 1)) d) - w * 10 ^ 12 : ℝ) <
      -6645002 * 10 ^ 6 * S := by
    have := (Int.cast_lt (R := ℝ)).2 hlt
    push_cast at this
    linarith
  have key : (2 * max Ul Ur - w / S) * (10 ^ 12 * S) < (-6645002 / 10 ^ 6) * (10 ^ 12 * S) := by
    have e : (2 * max Ul Ur - w / S) * (10 ^ 12 * S) = 2 * (max Ul Ur * (10 ^ 12 * S)) -
        w * 10 ^ 12 := by field_simp
    rw [e]
    have e2 : (-6645002 / 10 ^ 6 : ℝ) * (10 ^ 12 * S) = -6645002 * 10 ^ 6 * S := by ring
    rw [e2]
    linarith
  exact hB.trans_lt (lt_of_mul_lt_mul_right key (by positivity))

/-! ### The rows of the table -/

/-- The checks on the cells `J_{j,d,k}, …, J_{j,d,k+n-1}`, given the upper bound `uL` for
`10¹² 2^64 U^ρ` at the left end of the first; each bound is computed once and passed on. -/
def blockAux (j d : ℕ) : ℕ → ℕ → ℤ → Bool
  | 0, _, _ => true
  | n + 1, k, uL =>
    let uR := uU (xL j d (k + 1)) d
    cellCheck j d k uL uR && blockAux j d n (k + 1) uR

/-- The checks on the cells of one row `(j, d, a, b)` of the refinement table. -/
def blockOK (B : ℕ × ℕ × ℕ × ℕ) : Bool :=
  blockAux B.1 B.2.1 (B.2.2.2 + 1 - B.2.2.1) B.2.2.1 (uU (xL B.1 B.2.1 B.2.2.1) B.2.1)

/-- If `blockAux j d n k` succeeds, then `cellCheck` succeeds on each of the cells
`J_{j,d,k}, …, J_{j,d,k+n-1}`. -/
theorem cellCheck_of_blockAux (j d : ℕ) :
    ∀ n k, blockAux j d n k (uU (xL j d k) d) = true → ∀ i < n,
      cellCheck j d (k + i) (uU (xL j d (k + i)) d) (uU (xL j d (k + i + 1)) d) = true := by
  intro n
  induction n with
  | zero => intro k _ i hi; omega
  | succ n ih =>
    intro k h i hi
    simp only [blockAux, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have := ih (k + 1) h.2 i (by omega)
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

/-- The rows `0, …, 7` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₀ : ((potTableBlocks.drop 0).take 8).all blockOK = true := by decide +kernel
/-- The rows `8, …, 15` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₁ : ((potTableBlocks.drop 8).take 8).all blockOK = true := by decide +kernel
/-- The rows `16, …, 23` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₂ : ((potTableBlocks.drop 16).take 8).all blockOK = true := by decide +kernel
/-- The rows `24, …, 31` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₃ : ((potTableBlocks.drop 24).take 8).all blockOK = true := by decide +kernel
/-- The rows `32, …, 39` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₄ : ((potTableBlocks.drop 32).take 8).all blockOK = true := by decide +kernel
/-- The rows `40, …, 47` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₅ : ((potTableBlocks.drop 40).take 8).all blockOK = true := by decide +kernel
/-- The rows `48, …, 55` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₆ : ((potTableBlocks.drop 48).take 8).all blockOK = true := by decide +kernel
/-- The rows `56, …, 63` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₇ : ((potTableBlocks.drop 56).take 8).all blockOK = true := by decide +kernel
/-- The rows `64, …, 71` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₈ : ((potTableBlocks.drop 64).take 8).all blockOK = true := by decide +kernel
/-- The rows `72, …, 79` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₉ : ((potTableBlocks.drop 72).take 8).all blockOK = true := by decide +kernel
/-- The rows `80, …, 87` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₁₀ : ((potTableBlocks.drop 80).take 8).all blockOK = true := by
  decide +kernel
/-- The rows `88, …, 95` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₁₁ : ((potTableBlocks.drop 88).take 8).all blockOK = true := by
  decide +kernel
/-- The rows `96, …, 103` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₁₂ : ((potTableBlocks.drop 96).take 8).all blockOK = true := by
  decide +kernel
/-- The rows `104, …, 111` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₁₃ : ((potTableBlocks.drop 104).take 8).all blockOK = true := by
  decide +kernel
/-- The rows `112, …, 119` of the refinement table pass `blockOK`. -/
theorem blockOK_chunk₁₄ : ((potTableBlocks.drop 112).take 8).all blockOK = true := by
  decide +kernel

/-- If the rows `n, …, n + 7` of the table and all rows from `n + 8` on pass `blockOK`, then all
rows from `n` on do. -/
theorem all_drop_of_chunk {n : ℕ} (h₁ : ((potTableBlocks.drop n).take 8).all blockOK = true)
    (h₂ : (potTableBlocks.drop (n + 8)).all blockOK = true) :
    (potTableBlocks.drop n).all blockOK = true := by
  rw [← List.take_append_drop 8 (potTableBlocks.drop n), List.all_append, h₁, List.drop_drop,
    h₂, Bool.and_self]

/-- Every row of the refinement table passes `blockOK`. -/
theorem all_blockOK : potTableBlocks.all blockOK = true := by
  have h : (potTableBlocks.drop 120).all blockOK = true := by
    rw [List.drop_eq_nil_of_le (by simp [potTableBlocks])]
    rfl
  have := all_drop_of_chunk blockOK_chunk₁₄ h
  have := all_drop_of_chunk blockOK_chunk₁₃ this
  have := all_drop_of_chunk blockOK_chunk₁₂ this
  have := all_drop_of_chunk blockOK_chunk₁₁ this
  have := all_drop_of_chunk blockOK_chunk₁₀ this
  have := all_drop_of_chunk blockOK_chunk₉ this
  have := all_drop_of_chunk blockOK_chunk₈ this
  have := all_drop_of_chunk blockOK_chunk₇ this
  have := all_drop_of_chunk blockOK_chunk₆ this
  have := all_drop_of_chunk blockOK_chunk₅ this
  have := all_drop_of_chunk blockOK_chunk₄ this
  have := all_drop_of_chunk blockOK_chunk₃ this
  have := all_drop_of_chunk blockOK_chunk₂ this
  have := all_drop_of_chunk blockOK_chunk₁ this
  have := all_drop_of_chunk blockOK_chunk₀ this
  rwa [List.drop_zero] at this

end Zeta5Irr.PotTableBound

namespace Zeta5Irr

open PotTableBound

set_option maxRecDepth 4000 in
/-- **The interval bound on the refinement table**: for every `(j, d, k) ∈ 𝒯`,
`𝓑(Aⱼ + (Aⱼ₊₁ - Aⱼ) k / 2^d, Aⱼ + (Aⱼ₊₁ - Aⱼ) (k + 1) / 2^d) < -6645002 / 10⁶`. -/
@[zeta5irr "lem_pot_table_bound"]
theorem potBound_potInterval_lt {j d k : ℕ} (h : (j, d, k) ∈ potTable) :
    potBound (potIntervalLeft ⟨j, lt_of_mem_potTable h⟩ d k)
      (potIntervalRight ⟨j, lt_of_mem_potTable h⟩ d k) < -6645002 / 10 ^ 6 := by
  obtain ⟨a, b, hB, hak, hkb⟩ := mem_potTable.1 h
  have hblk : blockOK (j, d, a, b) = true := List.all_eq_true.1 all_blockOK _ hB
  have := cellCheck_of_blockAux j d (b + 1 - a) a hblk (k - a) (by omega)
  rw [show a + (k - a) = k by omega] at this
  exact potBound_lt_of_cellCheck _ this

end Zeta5Irr
