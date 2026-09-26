/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.DegreePositivity.WeightBound
public import Zeta5Irr.DegreePositivity.WeightPos
public import Zeta5Irr.Measure.V
public import Zeta5Irr.RealDeterminant.RiemannSum

/-!
# The weighted rational factor of the real Gram integral, after scaling

After the substitution `y = K √t`, the integrand of the real Gram integral carries the factor
`D_N(K²t)⁶ / D_K(K²t) · w(K√t) · K / (2√t)`. This file bounds it, for every `t > 0`, by
`4096 e¹² K^{12N - 2K + 18} t^{-1/2} (1 + √t)⁵ e^{-K V(t)}`, where `V` is the external field.

The weight is bounded by `w(y) ≤ 8192 (1 + y)⁵ e^{-2πy}`. For the rational factor one pulls
`K²` out of every factor, `D_m(K²t) = K^{2m} ∏_{j=1}^m (t + (j/K)²)`, and compares the
logarithms of the remaining products with `K ∫ log (t + u²) du` by the two Riemann-sum
bounds. The factors `e^{±2πK√t}` then cancel.

## Main results

* `Zeta5Irr.prod_Icc_sq_mul_add_sq`: `∏_{j=1}^m (k²t + j²) = k^{2m} ∏_{j=1}^m (t + (j/k)²)`.
* `Zeta5Irr.eval_poleProductRange_pow_div_mul_weight_le`: the bound for any `1 ≤ N ≤ K`
  with `N / K = α`.
* `Zeta5Irr.eval_poleProductRange_innerDegree_pow_div_mul_weight_le`: the bound for the
  parameters `K = 40 n`, `N = 3 n`.

## Implementation notes

The source's argument uses of the parameters only `1 ≤ N ≤ K` and `N / K = α`, so the bound
is first proved under exactly these hypotheses. The exponent `12N - 2K + 18` is negative for
the actual parameters, so the power of `K` is an integer power.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (The Gram integral and scaling).
-/

@[expose] public section

namespace Zeta5Irr

open Real Finset

/-- Rescaling: `∏_{j=1}^m (k²t + j²) = k^{2m} ∏_{j=1}^m (t + (j/k)²)` for `k ≠ 0`. -/
theorem prod_Icc_sq_mul_add_sq {k : ℝ} (hk : k ≠ 0) (m : ℕ) (t : ℝ) :
    ∏ j ∈ Icc 1 m, (k ^ 2 * t + (j : ℝ) ^ 2) =
      k ^ (2 * m) * ∏ j ∈ Icc 1 m, (t + ((j : ℝ) / k) ^ 2) := by
  have : ∀ j ∈ Icc 1 m, k ^ 2 * t + (j : ℝ) ^ 2 = k ^ 2 * (t + ((j : ℝ) / k) ^ 2) := by
    intro j _; field_simp
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, Nat.card_Icc, ← pow_mul]
  simp

/-- For naturals `1 ≤ N ≤ K` with `N / K = α` and every `t > 0`,
`D_N(K²t)⁶ / D_K(K²t) · w(K√t) · K / (2√t)
  ≤ 4096 e¹² K^{12N - 2K + 18} t^{-1/2} (1 + √t)⁵ e^{-K V(t)}`. -/
theorem eval_poleProductRange_pow_div_mul_weight_le {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (hα : (N : ℝ) / K = innerRatio) {t : ℝ} (ht : 0 < t) :
    (poleProductRange N ℝ).eval ((K : ℝ) ^ 2 * t) ^ 6 /
        (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t) * weight (K * √t) * (K / (2 * √t)) ≤
      4096 * rexp 12 * (K : ℝ) ^ (12 * (N : ℤ) - 2 * K + 18) * t ^ (-(1 / 2 : ℝ)) *
        (1 + √t) ^ 5 * rexp (-(K * externalField t)) := by
  set k : ℝ := (K : ℝ) with hkdef
  have hK1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hN.trans hNK
  have hk : 0 < k := by linarith
  set s := √t with hs
  have hs0 : 0 < s := sqrt_pos.2 ht
  have hrp : t ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [rpow_neg ht.le, ← sqrt_eq_rpow]
  set P := ∏ j ∈ Icc 1 N, (t + ((j : ℝ) / k) ^ 2) with hP
  set Q := ∏ j ∈ Icc 1 K, (t + ((j : ℝ) / k) ^ 2) with hQ
  have hPpos : 0 < P := prod_pos fun _ _ => by positivity
  have hQpos : 0 < Q := prod_pos fun _ _ => by positivity
  rw [eval_poleProductRange, eval_poleProductRange, prod_Icc_sq_mul_add_sq hk.ne',
    prod_Icc_sq_mul_add_sq hk.ne', ← hP, ← hQ, hrp]
  -- the rational factor
  have hlogP : log P = ∑ j ∈ Icc 1 N, log (t + ((j : ℝ) / k) ^ 2) :=
    log_prod fun _ _ => by positivity
  have hlogQ : log Q = ∑ j ∈ Icc 1 K, log (t + ((j : ℝ) / k) ^ 2) :=
    log_prod fun _ _ => by positivity
  have h1 := sum_log_add_sq_sub_integral_le hN (by rw [hkdef]; exact_mod_cast hNK) ht.le
    (K := k)
  have h2 := integral_log_add_sq_le_sum hk K ht.le
  rw [← hkdef, div_self hk.ne'] at h2
  rw [hα] at h1
  have hV : externalField t = 2 * π * s + (∫ u in (0 : ℝ)..1, log (t + u ^ 2)) -
      6 * ∫ u in (0 : ℝ)..(innerRatio : ℝ), log (t + u ^ 2) := rfl
  have hPQ : P ^ 6 / Q ≤ k ^ 12 * rexp 12 * rexp (-(k * externalField t)) *
      rexp (2 * π * k * s) := by
    have : P ^ 6 / Q = rexp (6 * log P - log Q) := by
      rw [exp_sub, exp_log hQpos, show 6 * log P = log (P ^ 6) by rw [log_pow]; norm_num,
        exp_log (by positivity)]
    rw [this, show k ^ 12 = rexp (12 * log k) by
      rw [← exp_log (pow_pos hk 12), log_pow]; norm_num, ← exp_add, ← exp_add, ← exp_add]
    apply exp_le_exp.2
    rw [hlogP, hlogQ, hV]
    nlinarith
  -- the weight factor
  have hw := weight_le (mul_pos hk hs0)
  have hw' : weight (k * s) ≤ 8192 * k ^ 5 * (1 + s) ^ 5 * rexp (-(2 * π * (k * s))) := by
    refine hw.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    rw [mul_assoc, ← mul_pow]
    gcongr
    nlinarith
  have hwpos := weight_pos (mul_pos hk hs0)
  have hzpow : (k ^ (2 * N)) ^ 6 / k ^ (2 * K) = k ^ (12 * (N : ℤ) - 2 * K) := by
    rw [← pow_mul, zpow_sub₀ hk.ne', ← zpow_natCast, ← zpow_natCast]
    push_cast; ring_nf
  have hrew : (k ^ (2 * N) * P) ^ 6 / (k ^ (2 * K) * Q) =
      k ^ (12 * (N : ℤ) - 2 * K) * (P ^ 6 / Q) := by
    rw [← hzpow]; field_simp
  rw [hrew]
  have hz18 : k ^ (12 * (N : ℤ) - 2 * K + 18) = k ^ (12 * (N : ℤ) - 2 * K) * k ^ 18 := by
    rw [zpow_add₀ hk.ne']; norm_cast
  rw [hz18]
  have hzpos : 0 < k ^ (12 * (N : ℤ) - 2 * K) := zpow_pos hk _
  calc k ^ (12 * (N : ℤ) - 2 * K) * (P ^ 6 / Q) * weight (k * s) * (k / (2 * s))
      ≤ k ^ (12 * (N : ℤ) - 2 * K) * (k ^ 12 * rexp 12 * rexp (-(k * externalField t)) *
          rexp (2 * π * k * s)) *
          (8192 * k ^ 5 * (1 + s) ^ 5 * rexp (-(2 * π * (k * s)))) * (k / (2 * s)) := by
        gcongr
    _ = _ := by
        rw [show 2 * π * (k * s) = 2 * π * k * s by ring, exp_neg (2 * π * k * s)]
        field_simp
        ring

/-- **The weighted rational factor after scaling.** For every `t > 0`, with `K = 40 n` and
`N = 3 n`,
`D_N(K²t)⁶ / D_K(K²t) · w(K√t) · K / (2√t)
  ≤ 4096 e¹² K^{12N - 2K + 18} t^{-1/2} (1 + √t)⁵ e^{-K V(t)}`. -/
@[zeta5irr "lem_real_weight_bound"]
theorem eval_poleProductRange_innerDegree_pow_div_mul_weight_le {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) :
    (poleProductRange (innerDegree n) ℝ).eval ((poleBound n : ℝ) ^ 2 * t) ^ 6 /
        (poleProductRange (poleBound n) ℝ).eval ((poleBound n : ℝ) ^ 2 * t) *
          weight (poleBound n * √t) * (poleBound n / (2 * √t)) ≤
      4096 * rexp 12 * (poleBound n : ℝ) ^ (12 * (innerDegree n : ℤ) - 2 * poleBound n + 18) *
        t ^ (-(1 / 2 : ℝ)) * (1 + √t) ^ 5 * rexp (-(poleBound n * externalField t)) :=
  eval_poleProductRange_pow_div_mul_weight_le (by simp [innerDegree]; omega)
    (by simp [innerDegree, poleBound]; omega)
    (by
      have : (n : ℝ) ≠ 0 := by positivity
      simp [innerDegree, poleBound, innerRatio]
      field_simp) ht

end Zeta5Irr
