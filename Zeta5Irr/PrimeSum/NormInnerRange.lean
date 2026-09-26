/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.Lp
public import Zeta5Irr.PrimeSum.GinAsymp
public import Zeta5Irr.PrimeSum.VpSKAsymp
public import Zeta5Irr.PrimeSum.NormRPwc
public import Zeta5Irr.PrimeSum.PartialSumPnt
public import Zeta5Irr.PrimeSum.NormThetaInterval
public import Zeta5Irr.LimitingFunctions.R

/-!
# The normalizing factor on the inner range of primes

Fix an integer `M ≥ 40`. For `K = 40 n` and a prime `p` with `K / M < p ≤ K / 3`, the local
exponent is `L_p(K, M) = v_p(S_K) + γ_p^in`. The asymptotics `|v_p(S_K) - p 𝒩(K/p)| ≤ 2M` and
`|γ_p^in - p Γ(K/p)| ≤ 10⁴ M²`, valid once `K ≥ 200 M²`, together with `R = -Γ - 𝒩` give
`|-L_p(K, M) - p R(K/p)| ≤ 10⁴ M² + 2M`. Summing against `log p` the error is at most
`(10⁴ M² + 2M) θ(K) ≤ (10⁴ M² + 2M) (log 4) K`, which is `o(K²)`, while the piecewise
continuity of `R` on `[3, M]` and the prime number theorem give
`K⁻² ∑_{K/M < p ≤ K/3} p R(K/p) log p → ∫_3^M R(x) x⁻³ dx`. Hence
```
K⁻² (-∑_{K/M < p ≤ K/3} L_p(K, M) log p) → ∫_3^M R(x) / x³ dx
```
as `K → ∞` through multiples of `40`, the sum being over primes.

## Main results

* `Zeta5Irr.abs_neg_localExponent_sub_le`: `|-L_p(K, M) - p R(K/p)| ≤ 10⁴ M² + 2M` on the inner
  range.
* `Zeta5Irr.tendsto_neg_sum_inner_localExponent_mul_log_div_sq`: the limit.

## Implementation notes

* `K = 40 n` is `Zeta5Irr.poleBound n`, and the limit is taken as `n → ∞`; the source's
  condition `K ≥ 200 M²` holds for all large `n`, so it does not appear in the statement.
* The primes `K / M < p ≤ K / 3` are those of `Finset.Ioc (K / M) (K / 3)` with natural
  division, since `K / M < p ↔ ⌊K / M⌋ < p` and `p ≤ K / 3 ↔ p ≤ ⌊K / 3⌋` for natural `p`.
* The error is bounded by `θ(K)` rather than the source's `θ(K / 3)`; either is `O(K)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8 (The growth of the normalizing factor).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology

/-- For an integer `M ≥ 40`, `K = 40 n ≥ 200 M²` and a prime `p` with `K / M < p ≤ K / 3`,
`|-L_p(K, M) - p R(K/p)| ≤ 10⁴ M² + 2M`. -/
theorem abs_neg_localExponent_sub_le {n M p : ℕ} (hp : p.Prime) (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : poleBound n < p * M)
    (hpu : 3 * p ≤ poleBound n) :
    |-(localExponent n M p : ℝ) - p * innerLimitingR ((poleBound n : ℝ) / p)| ≤
      10 ^ 4 * M ^ 2 + 2 * M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hplR : (poleBound n : ℝ) / M < p := by
    rw [div_lt_iff₀ hM0]; exact_mod_cast hpl
  have hodd : Odd p := by
    refine hp.eq_two_or_odd'.resolve_left ?_
    rintro rfl
    nlinarith
  have h₁ := abs_padicValRat_scalingFactor_sub_mul_scalarLimitingFunction_le_of_le hp hM hK hplR
  have h₂ := abs_innerExponent_sub_le hodd hM hK (by rwa [mul_comm]) hpu
  rw [localExponent_of_inner hpl hpu, innerLimitingR_def]
  push_cast
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **The inner range of the normalizing factor.** For an integer `M ≥ 40`,
`K⁻² (-∑_{K/M < p ≤ K/3} L_p(K, M) log p) → ∫_3^M R(x) / x³ dx` as `K = 40 n → ∞`, the sum
being over primes. -/
@[zeta5irr "lem_norm_inner_range"]
theorem tendsto_neg_sum_inner_localExponent_mul_log_div_sq {M : ℕ} (hM : 40 ≤ M) :
    Tendsto (fun n : ℕ =>
      (-∑ p ∈ Finset.Ioc (poleBound n / M) (poleBound n / 3) with p.Prime,
        (localExponent n M p : ℝ) * Real.log p) / (poleBound n : ℝ) ^ 2) atTop
      (𝓝 (∫ x in (3 : ℝ)..M, innerLimitingR x / x ^ 3)) := by
  have hM3 : (3 : ℝ) < M := by exact_mod_cast (show 3 < M by omega)
  have hK : Tendsto (fun n : ℕ => (poleBound n : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => ?_) tendsto_id)
    simp [poleBound]; omega
  have hmain := ((piecewiseContinuousOn_innerLimitingR hM3).tendsto_sum_prime_mul_log_div_sq
    (by norm_num : (0 : ℝ) < 3)).comp hK
  have hfloor : ∀ n : ℕ, ∀ d : ℕ, ⌊(poleBound n : ℝ) / d⌋₊ = poleBound n / d := fun n d =>
    Nat.floor_div_eq_div _ _
  simp only [Function.comp_def] at hmain
  set C : ℝ := 10 ^ 4 * M ^ 2 + 2 * M with hC
  have herr : Tendsto (fun n : ℕ =>
      (-∑ p ∈ Finset.Ioc (poleBound n / M) (poleBound n / 3) with p.Prime,
        (localExponent n M p : ℝ) * Real.log p) / (poleBound n : ℝ) ^ 2 -
      (∑ p ∈ Finset.Ioc (poleBound n / M) (poleBound n / 3) with p.Prime,
        (p : ℝ) * innerLimitingR (poleBound n / p) * Real.log p) / (poleBound n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => C * Real.log 4 * (poleBound n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hK).const_mul (C * Real.log 4)
    refine squeeze_zero_norm' ?_ hlim
    have hev : ∀ᶠ n : ℕ in atTop, 200 * M ^ 2 ≤ poleBound n := by
      refine eventually_atTop.2 ⟨200 * M ^ 2, fun n hn => ?_⟩
      simp only [poleBound]; omega
    filter_upwards [hev] with n hn
    have hK0 : (0 : ℝ) < poleBound n := by
      have : 0 < poleBound n := lt_of_lt_of_le (by positivity) hn
      exact_mod_cast this
    rw [← sub_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, Real.norm_eq_abs,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < (poleBound n : ℝ) ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    calc |∑ p ∈ Finset.Ioc (poleBound n / M) (poleBound n / 3) with p.Prime,
          (-((localExponent n M p : ℝ) * Real.log p) -
            (p : ℝ) * innerLimitingR (poleBound n / p) * Real.log p)|
        = |∑ p ∈ Finset.Ioc (poleBound n / M) (poleBound n / 3) with p.Prime,
          (-(localExponent n M p : ℝ) - p * innerLimitingR (poleBound n / p)) * Real.log p| := by
          congr 1; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ C * (Real.log 4 * (poleBound n / 3 : ℕ)) := by
          refine abs_sum_prime_mul_log_le (by positivity) _ fun p hp hpp => ?_
          rw [Finset.mem_Ioc] at hp
          exact abs_neg_localExponent_sub_le hpp hM hn ((Nat.div_lt_iff_lt_mul (by omega)).1 hp.1)
            (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by norm_num)).1 hp.2)
      _ ≤ C * (Real.log 4 * poleBound n) := by
          gcongr
          exact_mod_cast Nat.div_le_self _ _
      _ = C * Real.log 4 * (poleBound n : ℝ)⁻¹ * (poleBound n : ℝ) ^ 2 := by
          field_simp
  have hfloor3 : ∀ n : ℕ, ⌊(poleBound n : ℝ) / 3⌋₊ = poleBound n / 3 := fun n => by
    exact_mod_cast hfloor n 3
  simp only [hfloor, hfloor3] at hmain
  simpa using hmain.add herr

end Zeta5Irr
