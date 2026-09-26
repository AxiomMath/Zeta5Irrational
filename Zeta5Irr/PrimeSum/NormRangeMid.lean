/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.Lp
public import Zeta5Irr.PrimeSum.NormThetaInterval
public import Mathlib.Algebra.Order.Star.Real

/-!
# The mid-range primes in the normalizing factor

Let `M ≥ 40` and `K = 40 n`. Every prime `p` with `√(5K) < p ≤ K / M` satisfies `p M ≤ K`, so
its local exponent is `L_p(K, M) = -6 h ⌊log_p (5K)⌋ - h v_p(24)`; moreover `p > 3` and
`p ≤ 5K < p²`, so `v_p(24) = 0` and `⌊log_p (5K)⌋ = 1`, whence `L_p(K, M) = -6 h`. The sum of
`-L_p(K, M) log p` over these primes is therefore `6 h (ϑ(K / M) - ϑ(√(5K)))`, and since
`h = λ K`, the prime number theorem `ϑ(y) / y → 1` together with Chebyshev's bound
`ϑ(y) ≤ y log 4` gives
```
(1 / K²) (-∑_{√(5K) < p ≤ K/M} L_p(K, M) log p) → 6 λ / M    (K → ∞, 40 ∣ K).
```

## Main results

* `Zeta5Irr.localExponent_eq_neg_six_mul_of_sqrt_lt`: `L_p(K, M) = -6 h` for a prime `p`
  with `√(5K) < p` and `p M ≤ K`.
* `Zeta5Irr.tendsto_theta_sqrt_div_atTop`: `ϑ(√(cK)) / K → 0` as `K → ∞`.
* `Zeta5Irr.tendsto_neg_sum_localExponent_mul_log_div_sq`: the limit above.

## Implementation notes

* Since `K = 40 n`, the limit over `K ∈ 40 ℤ` is the limit `n → ∞`, with `K` written
  `Zeta5Irr.poleBound n`. The source's side condition `K ≥ 200 M²` holds for all large `n`,
  so it does not affect the limit and is not imposed.
* The primes `√(5K) < p ≤ K / M` are those of `Finset.Ioc ⌊√(5K)⌋₊ ⌊K / M⌋₊`.
* The hypothesis `M ≥ 40` is not needed: the argument works for every `M ≥ 1`, and for `M = 0`
  both sides vanish with Lean's conventions `⌊K / 0⌋₊ = 0` and `6 λ / 0 = 0`. The theorem is
  therefore stated for every natural number `M`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8 (The growth of the normalizing factor).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology Finset

/-- If `p` is a prime with `√(5K) < p` and `p M ≤ K` for some `M ≥ 1`, then
`L_p(K, M) = -6 h`: here `⌊log_p (5K)⌋ = 1` and `v_p(24) = 0`. -/
theorem localExponent_eq_neg_six_mul_of_sqrt_lt {n M p : ℕ} (hp : p.Prime) (hM : 0 < M)
    (hlo : √(5 * poleBound n : ℝ) < p) (hhi : p * M ≤ poleBound n) :
    localExponent n M p = -6 * matrixOrder n := by
  have hpK : p ≤ poleBound n := le_trans (Nat.le_mul_of_pos_right p hM) hhi
  have hsq : 5 * poleBound n < p ^ 2 := by
    have h := (Real.sqrt_lt' (by exact_mod_cast hp.pos)).1 hlo
    exact_mod_cast h
  have hp5 : 5 < p := by nlinarith
  have hlog : Nat.log p (5 * poleBound n) = 1 := by
    rw [Nat.log_eq_iff (by norm_num)]
    exact ⟨by rw [pow_one]; omega, hsq⟩
  have hval : padicValNat p 24 = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> first | omega | norm_num at hp
  rw [localExponent_of_mul_le_natLog hhi, hlog, hval]
  push_cast
  ring

/-- `ϑ(√(cK)) / K → 0` as `K → ∞`, by Chebyshev's bound `ϑ(y) ≤ y log 4`. -/
theorem tendsto_theta_sqrt_div_atTop (c : ℝ) :
    Tendsto (fun K : ℝ ↦ Chebyshev.theta √(c * K) / K) atTop (𝓝 0) := by
  have hs : Tendsto (fun K : ℝ ↦ Real.log 4 * √|c| * (√K)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul
      (Real.log 4 * √|c|)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with K hK
    exact div_nonneg (Chebyshev.theta_nonneg _) hK.le
  · filter_upwards [eventually_gt_atTop 0] with K hK
    rw [div_le_iff₀ hK]
    calc Chebyshev.theta √(c * K) ≤ Real.log 4 * √(c * K) :=
          Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg _)
      _ ≤ Real.log 4 * (√|c| * √K) := by
          gcongr
          rw [← Real.sqrt_mul (abs_nonneg c)]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_abs_self c) hK.le)
      _ = Real.log 4 * √|c| * (√K)⁻¹ * K := by
          have := Real.sqrt_pos.2 hK
          field_simp
          rw [Real.sq_sqrt hK.le]

/-- For `K = 40 n` and every `M`, `(1 / K²) (-∑_{√(5K) < p ≤ K/M} L_p(K, M) log p) → 6 λ / M`
as `n → ∞`, the sum being over primes. -/
@[zeta5irr "lem_norm_range_mid"]
theorem tendsto_neg_sum_localExponent_mul_log_div_sq (M : ℕ) :
    Tendsto (fun n : ℕ ↦ -(∑ p ∈ Ioc ⌊√(5 * poleBound n : ℝ)⌋₊ ⌊(poleBound n : ℝ) / M⌋₊
        with p.Prime, (localExponent n M p : ℝ) * Real.log p) / (poleBound n : ℝ) ^ 2)
      atTop (𝓝 (6 * orderRatio / M)) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hK : Tendsto (fun n : ℕ ↦ (40 * n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlim : Tendsto (fun K : ℝ ↦ 6 * (37 / 40) *
      (Chebyshev.theta ((M : ℝ)⁻¹ * K) / K - Chebyshev.theta √(5 * K) / K)) atTop
      (𝓝 (6 * orderRatio / M)) := by
    have := ((tendsto_theta_mul_div_atTop (inv_nonneg.2 (Nat.cast_nonneg M (α := ℝ)))).sub
      (tendsto_theta_sqrt_div_atTop 5)).const_mul (6 * (37 / 40))
    convert this using 2
    simp [orderRatio]
    ring
  refine (hlim.comp hK).congr' ?_
  filter_upwards [eventually_ge_atTop (M ^ 2), eventually_gt_atTop 0] with n hn hn0
  have hKn : (poleBound n : ℝ) = 40 * n := by simp [poleBound]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnM : (M : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hle : √(5 * poleBound n : ℝ) ≤ (poleBound n : ℝ) / M := by
    rw [← Real.sqrt_sq (div_nonneg (Nat.cast_nonneg (poleBound n)) hMr.le)]
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow, le_div_iff₀ (by positivity), hKn]
    nlinarith
  have hsum : ∑ p ∈ Ioc ⌊√(5 * poleBound n : ℝ)⌋₊ ⌊(poleBound n : ℝ) / M⌋₊ with p.Prime,
      (localExponent n M p : ℝ) * Real.log p =
      ∑ p ∈ Ioc ⌊√(5 * poleBound n : ℝ)⌋₊ ⌊(poleBound n : ℝ) / M⌋₊ with p.Prime,
      (-6 * matrixOrder n : ℝ) * Real.log p := by
    refine sum_congr rfl fun p hp => ?_
    simp only [mem_filter, mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hp⟩ := hp
    have hlo := (Nat.floor_lt (Real.sqrt_nonneg _)).1 h1
    have hhi := (Nat.le_floor_iff (by positivity)).1 h2
    rw [le_div_iff₀ hMr] at hhi
    rw [localExponent_eq_neg_six_mul_of_sqrt_lt hp hM hlo (by exact_mod_cast hhi)]
    push_cast
    ring
  rw [hsum, ← mul_sum, sum_Ioc_floor_prime_log_eq_theta_sub hle]
  simp only [Function.comp_apply, hKn, matrixOrder, inv_mul_eq_div]
  push_cast
  field_simp

end Zeta5Irr
