/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormAbel
public import Zeta5Irr.PrimeSum.NormThetaPnt
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# The asymptotic `∑_{p ≤ Y} p log p ∼ Y² / 2`

As a consequence of the prime number theorem `ϑ(y) / y → 1`, the sum `∑_{p ≤ Y} p log p` over
primes satisfies `Y⁻² ∑_{p ≤ Y} p log p → 1 / 2` as `Y → ∞`.

Abel summation with `φ(t) = t` gives `∑_{p ≤ Y} p log p = Y ϑ(Y) - ∫_1^Y ϑ(t) dt`. The first term
divided by `Y²` is `ϑ(Y) / Y → 1`. For the second, `ϑ(t) - t = o(t)` integrates to
`∫_1^Y (ϑ(t) - t) dt = o(Y²)`, so `Y⁻² ∫_1^Y ϑ(t) dt → 1 / 2`.

## Main results

* `Zeta5Irr.isLittleO_integral_theta_sub_id`: `∫_1^Y (ϑ(t) - t) dt = o(Y²)` as `Y → ∞`.
* `Zeta5Irr.tendsto_integral_theta_div_sq`: `Y⁻² ∫_1^Y ϑ(t) dt → 1 / 2` as `Y → ∞`.
* `Zeta5Irr.tendsto_sum_primesLE_mul_log_div_sq`: `Y⁻² ∑_{p ≤ Y} p log p → 1 / 2` as `Y → ∞`.

## Implementation notes

* `ϑ` is Mathlib's `Chebyshev.theta`, and the primes `p ≤ Y` are enumerated as
  `Nat.primesLE ⌊Y⌋₊`.
* The source bounds `∫_1^Y ϑ` between `(1 ± ε)` multiples of `Y² / 2` up to a constant and takes
  `liminf` and `limsup`; we phrase the same estimate as a little-o bound for `∫_1^Y (ϑ(t) - t) dt`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.7 (The prime number theorem).
-/

@[expose] public section

namespace Zeta5Irr

open Real MeasureTheory Set Filter Asymptotics Topology Chebyshev
open scoped Interval

/-- Chebyshev's `ϑ` is interval integrable on every interval, being monotone. -/
theorem intervalIntegrable_theta (a b : ℝ) : IntervalIntegrable θ volume a b :=
  theta_mono.intervalIntegrable

/-- As a consequence of the prime number theorem, `∫_1^Y (ϑ(t) - t) dt = o(Y²)` as `Y → ∞`. -/
theorem isLittleO_integral_theta_sub_id :
    (fun Y : ℝ ↦ ∫ t in 1..Y, (θ t - t)) =o[atTop] fun Y ↦ Y ^ 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t ↦ θ t - t) volume a b := fun a b ↦
    (intervalIntegrable_theta a b).sub (continuous_id.intervalIntegrable a b)
  refine isLittleO_iff.2 fun c hc ↦ ?_
  have hev : ∀ᶠ t : ℝ in atTop, |θ t / t - 1| ≤ c ∧ 1 ≤ t :=
    ((tendsto_order.1 (tendsto_theta_div_atTop.sub_const 1 |>.abs)).2 c
      (by simpa using hc)).mono (fun _ h ↦ h.le) |>.and (eventually_ge_atTop 1)
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hev
  have ht₀1 : 1 ≤ t₀ := (ht₀ t₀ le_rfl).2
  set C := |∫ t in 1..t₀, (θ t - t)|
  have hbd : ∀ t, t₀ ≤ t → |θ t - t| ≤ c * t := fun t ht ↦ by
    obtain ⟨h1, h2⟩ := ht₀ t ht
    have htpos : 0 < t := by linarith
    have : θ t / t - 1 = (θ t - t) / t := by field_simp
    rw [this, abs_div, abs_of_pos htpos, div_le_iff₀ htpos] at h1
    exact h1
  filter_upwards [eventually_ge_atTop t₀, eventually_ge_atTop (Real.sqrt (2 * C / c))]
    with Y hY hYC
  have hY0 : 0 ≤ Y := by linarith
  have hsq : 2 * C / c ≤ Y ^ 2 := by
    have := Real.sqrt_le_sqrt (le_of_eq (rfl : Y ^ 2 = Y ^ 2))
    rw [Real.sqrt_sq hY0] at this
    calc 2 * C / c ≤ Real.sqrt (2 * C / c) ^ 2 := by
          rw [Real.sq_sqrt (div_nonneg (by positivity) hc.le)]
      _ ≤ Y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hYC 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 1 t₀) (hint t₀ Y)
  have htail : ‖∫ t in t₀..Y, (θ t - t)‖ ≤ ∫ t in t₀..Y, c * t :=
    intervalIntegral.norm_integral_le_of_norm_le hY
      (Eventually.of_forall fun t ht ↦ by
        simpa [Real.norm_eq_abs] using hbd t ht.1.le)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, integral_id] at htail
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg Y), ← hsplit]
  have hCle : C ≤ c * Y ^ 2 / 2 := by
    rw [div_le_iff₀ hc] at hsq; linarith
  calc |(∫ t in 1..t₀, (θ t - t)) + ∫ t in t₀..Y, (θ t - t)|
      ≤ C + |∫ t in t₀..Y, (θ t - t)| := abs_add_le _ _
    _ ≤ C + c * ((Y ^ 2 - t₀ ^ 2) / 2) := by rw [← Real.norm_eq_abs]; linarith
    _ ≤ c * Y ^ 2 := by nlinarith [sq_nonneg t₀]

/-- As a consequence of the prime number theorem, `Y⁻² ∫_1^Y ϑ(t) dt → 1 / 2` as `Y → ∞`. -/
theorem tendsto_integral_theta_div_sq :
    Tendsto (fun Y : ℝ ↦ (∫ t in 1..Y, θ t) / Y ^ 2) atTop (𝓝 (1 / 2)) := by
  have h1 := isLittleO_integral_theta_sub_id.tendsto_div_nhds_zero
  have h2 : Tendsto (fun Y : ℝ ↦ 1 / 2 - (Y ^ 2)⁻¹ / 2) atTop (𝓝 (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).div_const 2)
  have h3 : Tendsto (fun Y : ℝ ↦ (∫ t in 1..Y, (θ t - t)) / Y ^ 2 + (1 / 2 - (Y ^ 2)⁻¹ / 2))
      atTop (𝓝 (1 / 2)) := by simpa using h1.add h2
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Y hY
  have hsub := intervalIntegral.integral_sub (intervalIntegrable_theta 1 Y)
    (continuous_id.intervalIntegrable (μ := volume) 1 Y)
  simp only [id] at hsub
  rw [hsub, integral_id]
  field_simp
  ring

/-- **`∑_{p ≤ Y} p log p ∼ Y² / 2`.** As a consequence of the prime number theorem,
`Y⁻² ∑_{p ≤ Y} p log p → 1 / 2` as `Y → ∞`, the sum being over primes. -/
@[zeta5irr "lem_norm_plogp"]
theorem tendsto_sum_primesLE_mul_log_div_sq :
    Tendsto (fun Y : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) * log p) / Y ^ 2) atTop
      (𝓝 (1 / 2)) := by
  have h := (tendsto_theta_div_atTop.sub tendsto_integral_theta_div_sq)
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  have hY0 : Y ≠ 0 := by positivity
  have habel := sum_primesLE_mul_log_eq_sub_integral (φ := id) (φ' := fun _ ↦ 1) hY
    continuousOn_id (fun t _ ↦ hasDerivAt_id t) intervalIntegrable_const
  simp only [id, one_mul] at habel
  rw [habel]
  field_simp

end Zeta5Irr
