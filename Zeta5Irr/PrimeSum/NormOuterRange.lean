/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.Lp
public import Zeta5Irr.ExactIntegrals.Iout
public import Zeta5Irr.PrimeSum.GoutAsymp
public import Zeta5Irr.PrimeSum.NormVpSKOuter
public import Zeta5Irr.PrimeSum.NormThetaPwc
public import Zeta5Irr.PrimeSum.NormPntOuter

/-!
# The normalizing factor on the outer range of primes

Fix an integer `M ≥ 40` (in fact `M ≥ 3` suffices). For `K = 40 n`, `h = 37 n` and a prime `p`
with `K / 3 < p ≤ 2h`, the local exponent is `L_p(K, M) = v_p(S_K) + γ_p^out` if `p ≤ K` and
`L_p(K, M) = v_p(S_K)` if `p > K`. The asymptotics of `v_p(S_K)` and of `γ_p^out` on this range,
together with `R₀(y) = d_rk(y) = 0` for `y > 1`, give
`|-L_p(K, M) - K Θ(p / K)| ≤ 40`, where `Θ` is the outer integrand. Summing against `log p`
the error is at most `40 θ(2h) ≤ 80 λ K log 4`, which is `o(K²)`, while the prime number
theorem for the piecewise continuous function `Θ` on `[1/3, 2λ]` gives
`K⁻¹ ∑_{K/3 < p ≤ 2h} Θ(p/K) log p → ∫_{1/3}^{2λ} Θ = I_out`. Hence
```
K⁻² (-∑_{K/3 < p ≤ 2h} L_p(K, M) log p) → I_out
```
as `K → ∞` through multiples of `40`, the sum being over primes.

## Main results

* `Zeta5Irr.abs_neg_localExponent_sub_mul_outerIntegrand_le`:
  `|-L_p(K, M) - K Θ(p/K)| ≤ 40` on the outer range.
* `Zeta5Irr.tendsto_neg_sum_outer_localExponent_mul_log_div_sq`: the limit.

## Implementation notes

* `K = 40 n` is `Zeta5Irr.poleBound n`, and the limit is taken as `n → ∞`; the source's
  condition `K ≥ 200 M²` holds for all large `n`, so it does not appear in the statement.
* The primes `K / 3 < p ≤ 2h` are those of `Finset.Ioc (K / 3) (2h)` with natural division.
* The statement is proved for every `M ≥ 3`: this is all that is needed for `3p > K` to force
  `pM > K`, so that `L_p(K, M)` is given by its third or fourth case.
* The source proves the convergence of `K⁻¹ ∑ Θ(p/K) log p` by applying the prime number
  theorem on `[1/3 + η, 2λ]` and letting `η → 0`. Since piecewise continuity only asks `Θ` to
  agree with a continuous function on each open piece, `Θ` is already piecewise continuous on
  `[1/3, 2λ]` (the closed form valid on `(1/3, 1/2]` is continuous on `[1/3, 1/2]`), and the
  prime number theorem applies there directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8 (The growth of the normalizing factor).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology Finset

/-- For `M ≥ 3`, `K = 40 n`, `h = 37 n` and a prime `p` with `K / 3 < p ≤ 2h`,
`|-L_p(K, M) - K Θ(p/K)| ≤ 40`, where `Θ` is the outer integrand. -/
theorem abs_neg_localExponent_sub_mul_outerIntegrand_le {n M p : ℕ} (hM : 3 ≤ M) (hp : p.Prime)
    (hp₁ : poleBound n < 3 * p) (hp₂ : p ≤ 2 * matrixOrder n) :
    |-(localExponent n M p : ℝ) - poleBound n * outerIntegrand (p / poleBound n)| ≤ 40 := by
  have hpK : (poleBound n : ℝ) / 3 < p := by
    have : (poleBound n : ℝ) < 3 * p := by exact_mod_cast hp₁
    linarith
  have hv := abs_neg_padicValRat_scalingFactor_sub_le hp hpK hp₂
  rw [← inv_div] at hv
  rcases le_or_gt p (poleBound n) with hle | hlt
  · have hg := abs_neg_outerExponent_sub_le hp₁ hle
    rw [localExponent_of_outer hM hp₁ hle, outerIntegrand]
    push_cast
    set X := -(padicValRat p (scalingFactor n) : ℝ) - poleBound n *
      (-2 * (orderRatio : ℝ) * ⌊((p : ℝ) / poleBound n)⁻¹⌋ +
        ∑ j ∈ Icc (1 : ℕ) 5, (2 * (orderRatio : ℝ) - j * p / poleBound n)⁺)
    set Y := -(outerExponent p (innerDegree n) (poleBound n) : ℝ) -
        poleBound n * (outerLimitingFunction (p / poleBound n) -
          rankDefect (p / poleBound n))
    calc _ = |X + Y| := by
          congr 1; simp only [X, Y, mul_div_assoc]; ring
      _ ≤ |X| + |Y| := abs_add_le _ _
      _ ≤ 40 := by linarith
  · have hK : (0 : ℝ) < poleBound n := by exact_mod_cast (show 0 < poleBound n by
      simp only [poleBound, matrixOrder] at hp₂ ⊢; omega)
    have hy : 1 < (p : ℝ) / poleBound n := by
      rw [one_lt_div hK]; exact_mod_cast hlt
    rw [localExponent_of_lt (by omega) hlt, outerIntegrand, outerLimitingFunction_of_one_lt hy,
      rankDefect_of_one_half_le (by linarith)]
    simp only [mul_div_assoc] at hv
    push_cast
    convert hv.trans (by norm_num : (20 : ℝ) ≤ 40) using 4
    ring

/-- **The outer range of the normalizing factor.** For an integer `M ≥ 3` (the source takes
`M ≥ 40`), `K⁻² (-∑_{K/3 < p ≤ 2h} L_p(K, M) log p) → I_out` as `K = 40 n → ∞`, the sum being
over primes. -/
@[zeta5irr "lem_norm_outer_range"]
theorem tendsto_neg_sum_outer_localExponent_mul_log_div_sq {M : ℕ} (hM : 3 ≤ M) :
    Tendsto (fun n : ℕ => -(∑ p ∈ Ioc (poleBound n / 3) (2 * matrixOrder n) with p.Prime,
      (localExponent n M p : ℝ) * Real.log p) / (poleBound n : ℝ) ^ 2) atTop
      (𝓝 outerIntegral) := by
  have hlam : (orderRatio : ℝ) = 37 / 40 := by norm_num [orderRatio]
  have hKn : ∀ n, (poleBound n : ℝ) = 40 * n := fun n => by simp [poleBound]
  have hKtend : Tendsto (fun n : ℕ => (poleBound n : ℝ)) atTop atTop := by
    simp only [hKn]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  -- the main term
  have hT : Tendsto (fun n : ℕ => (∑ p ∈ Ioc (poleBound n / 3) (2 * matrixOrder n) with p.Prime,
      outerIntegrand (p / poleBound n) * Real.log p) / poleBound n) atTop
      (𝓝 outerIntegral) := by
    refine (((piecewiseContinuousOn_outerIntegrand_of_le le_rfl (by norm_num [hlam])
      ).tendsto_sum_prime_mul_log_div_atTop (by norm_num)).comp hKtend).congr fun n => ?_
    have h₁ : ⌊(1 / 3 : ℝ) * poleBound n⌋₊ = poleBound n / 3 := by
      rw [one_div_mul_eq_div, Nat.floor_div_ofNat, Nat.floor_natCast]
    have h₂ : ⌊2 * (orderRatio : ℝ) * poleBound n⌋₊ = 2 * matrixOrder n := by
      rw [hlam, hKn, show 2 * (37 / 40 : ℝ) * (40 * n) = ((2 * matrixOrder n : ℕ) : ℝ) by
        simp [matrixOrder]; ring, Nat.floor_natCast]
    simp only [Function.comp_apply, h₁, h₂]
  -- the error term
  have hE : Tendsto (fun n : ℕ =>
      (-(∑ p ∈ Ioc (poleBound n / 3) (2 * matrixOrder n) with p.Prime,
        (localExponent n M p : ℝ) * Real.log p) -
      poleBound n * ∑ p ∈ Ioc (poleBound n / 3) (2 * matrixOrder n) with p.Prime,
        outerIntegrand (p / poleBound n) * Real.log p) / (poleBound n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (74 * Real.log 4 / 40))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s := {p ∈ Ioc (poleBound n / 3) (2 * matrixOrder n) | p.Prime}
    have hsum : -(∑ p ∈ s, (localExponent n M p : ℝ) * Real.log p) -
        poleBound n * ∑ p ∈ s, outerIntegrand (p / poleBound n) * Real.log p =
        ∑ p ∈ s, (-(localExponent n M p : ℝ) - poleBound n * outerIntegrand (p / poleBound n)) *
          Real.log p := by
      rw [mul_sum, ← sum_neg_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun p _ => by ring
    have hbd : |∑ p ∈ s, (-(localExponent n M p : ℝ) -
        poleBound n * outerIntegrand (p / poleBound n)) * Real.log p| ≤
        40 * (Real.log 4 * (2 * matrixOrder n : ℕ)) :=
      abs_sum_prime_mul_log_le (by norm_num) _ fun p hp hpp => by
        rw [mem_Ioc] at hp
        exact abs_neg_localExponent_sub_mul_outerIntegrand_le hM hpp (by omega) hp.2
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [Real.norm_eq_abs, abs_div, hsum, abs_of_nonneg (sq_nonneg (poleBound n : ℝ))]
    refine (div_le_div_of_nonneg_right hbd (sq_nonneg _)).trans ?_
    rw [hKn, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast [matrixOrder]
    nlinarith
  rw [← zero_add outerIntegral]
  refine (hE.add hT).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hK : (poleBound n : ℝ) ≠ 0 := by
    rw [hKn]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  field_simp
  ring

end Zeta5Irr
