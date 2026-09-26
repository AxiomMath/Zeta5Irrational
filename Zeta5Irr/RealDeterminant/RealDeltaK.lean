/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.RealScaledIntegral
public import Zeta5Irr.RealDeterminant.ConfigBoundField
public import Zeta5Irr.RealDeterminant.RealGamma652

/-!
# The bound for `log Δ_K(ξ)`

Let `ξ = ζ(5)`, `K = 40 n`, `N = 3 n`, `h = 37 n`, `λ = 37 / 40`, let `V` be the external
field and `ρ` the rational arcsine measure. Then
`log Δ_K(ξ) ≤ 2 h (h + 6N - K) log K + (-1329 λ / 200 - I(ρ)) K² + 18 h log K + 160 h`.

The integrand of the scaled multiple integral is bounded almost everywhere on `(0, ∞)^h`:
off the null set where two coordinates coincide, the configuration bound with the external
field gives
`∏_{i<j} (t_i - t_j)² ∏_i e^{-K V(t_i)} ≤ E ∏_i e^{-√t_i}` with
`E = exp((-1329 λ / 200 - I(ρ)) K² + (120 + √2) h + 2 h log K)`. The resulting product of
one-variable integrals is `652^h`. Taking logarithms in the scaled integral bound, which is
legitimate since `Δ_K(ξ) > 0`, and estimating
`log 4096 + 12 + 120 + √2 + log 652 < 160` and `log h! ≥ 0` gives the statement.

## Main results

* `Zeta5Irr.ae_injective_pi`: almost every point of `ι → ℝ` has pairwise distinct coordinates.
* `Zeta5Irr.integral_prod_sub_sq_mul_prod_exp_externalField_le`: the scaled integral is at
  most `E · 652^h`.
* `Zeta5Irr.log_aeval_gramDet_le`: the bound for `log Δ_K(ξ)`.

## Implementation notes

The measure-zero set of configurations with a repeated coordinate is handled as a finite
union of proper linear subspaces `{t | t_i = t_j}`, each null for the additive Haar measure
`volume`; the product of one-variable integrals is Fubini's theorem for product functions on
the product of the restricted measures, rather than Tonelli's theorem for lower integrals.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (The Gram integral and scaling).
-/

@[expose] public section

open Real MeasureTheory Set Polynomial

namespace Zeta5Irr

/-- Almost every point of `ι → ℝ` has pairwise distinct coordinates. -/
theorem ae_injective_pi {ι : Type*} [Fintype ι] :
    ∀ᵐ t ∂(volume : Measure (ι → ℝ)), Function.Injective t := by
  classical
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ i : ι, ⋃ j : ι, ⋃ (_ : i ≠ j),
    ((LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i -
      LinearMap.proj j) : Submodule ℝ (ι → ℝ)) : Set (ι → ℝ))) ?_ ?_
  · intro t ht
    simp only [Function.Injective, not_forall, mem_ofPred_eq] at ht
    obtain ⟨i, j, hij, hne⟩ := ht
    simp only [mem_iUnion, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.proj_apply]
    exact ⟨i, j, hne, sub_eq_zero.2 hij⟩
  · refine measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => Measure.addHaar_submodule _ _ ?_
    intro htop
    have : Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) ∈ LinearMap.ker
        (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i - LinearMap.proj j) := by
      rw [htop]
      trivial
    simp [LinearMap.mem_ker, Ne.symm hij] at this

/-- For pairwise distinct `t i`, the squared Vandermonde product is the exponential of twice
the sum of the logarithms of the gaps. -/
theorem prod_Ioi_sub_sq_eq_exp {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderTop ι] {t : ι → ℝ} (ht : Function.Injective t) :
    ∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2 =
      rexp (2 * ∑ i, ∑ j ∈ Finset.Ioi i, log |t i - t j|) := by
  rw [Finset.mul_sum, exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, exp_sum]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hne : t i - t j ≠ 0 := sub_ne_zero.2 fun h => (Finset.mem_Ioi.1 hj).ne (ht h)
  rw [show (2 : ℝ) * log |t i - t j| = log (|t i - t j| ^ 2) by rw [log_pow]; norm_num,
    exp_log (by positivity), sq_abs]

/-- On `(0, ∞)^h`, the integral of the scaled integrand is at most `E · 652^h`, where
`E = exp((-1329 λ / 200 - I(ρ)) K² + (120 + √2) h + 2 h log K)`. -/
theorem integral_prod_sub_sq_mul_prod_exp_externalField_le {n : ℕ} (hn : 0 < n) :
    ∫ t in univ.pi fun _ : Fin (matrixOrder n) => Ioi (0 : ℝ),
        (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
          ∏ i, rexp (-(poleBound n * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) *
            (1 + √(t i)) ^ 5 ≤
      rexp ((-1329 * (orderRatio : ℝ) / 200 - logEnergy (rho.map ((↑) : ℝ → ℂ))) *
          (poleBound n : ℝ) ^ 2 +
        (120 + √2) * matrixOrder n + 2 * matrixOrder n * log (poleBound n)) *
        652 ^ matrixOrder n := by
  set S := univ.pi fun _ : Fin (matrixOrder n) => Ioi (0 : ℝ)
  set B : ℝ := (-1329 * (orderRatio : ℝ) / 200 - logEnergy (rho.map ((↑) : ℝ → ℂ))) *
    (poleBound n : ℝ) ^ 2 + (120 + √2) * matrixOrder n + 2 * matrixOrder n * log (poleBound n)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hK1 : (1 : ℝ) ≤ poleBound n := by exact_mod_cast poleBound_pos hn
  let g : ℝ → ℝ := fun s => s ^ (-(1 / 2 : ℝ)) * (1 + √s) ^ 5 * rexp (-√s)
  have hg : IntegrableOn g (Ioi 0) := Integrable.of_integral_ne_zero (by
    rw [integral_rpow_neg_half_mul_one_add_sqrt_pow_five_mul_exp_neg_sqrt]; norm_num)
  have hrestr : volume.restrict S = Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hG : Integrable (fun t : Fin (matrixOrder n) → ℝ => ∏ i, g (t i))
      (volume.restrict S) := by
    rw [hrestr]
    exact Integrable.fintype_prod fun _ => hg
  have hGint : ∫ t in S, ∏ i, g (t i) = 652 ^ matrixOrder n := by
    rw [hrestr, integral_fintype_prod_eq_prod (f := fun _ => g)]
    simp only [g, integral_rpow_neg_half_mul_one_add_sqrt_pow_five_mul_exp_neg_sqrt,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbound : ∀ᵐ t ∂(volume.restrict S),
      (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
          ∏ i, rexp (-(poleBound n * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) *
            (1 + √(t i)) ^ 5 ≤ rexp B * ∏ i, g (t i) := by
    filter_upwards [ae_restrict_of_ae (ae_injective_pi (ι := Fin (matrixOrder n))),
      ae_restrict_mem hS] with t hinj ht
    have ht0 : ∀ i, 0 < t i := fun i => ht i (mem_univ i)
    have key := two_mul_sum_log_abs_sub_sub_externalField_add_sum_sqrt_le hn
      (fun i => (ht0 i).le) hinj
    have hA : ∏ i, rexp (-(poleBound n * externalField (t i))) =
        rexp (-(poleBound n * ∑ i, externalField (t i))) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, exp_sum]
    have hX : ∏ i, rexp (-√(t i)) = rexp (-∑ i, √(t i)) := by
      rw [← Finset.sum_neg_distrib, exp_sum]
    simp only [g, Finset.prod_mul_distrib]
    rw [prod_Ioi_sub_sq_eq_exp hinj, hA, hX]
    have hR : 0 ≤ (∏ i, t i ^ (-(1 / 2 : ℝ))) * ∏ i, (1 + √(t i)) ^ 5 :=
      mul_nonneg (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity)
        (Finset.prod_nonneg fun i _ => by positivity)
    have hE : rexp (2 * ∑ i, ∑ j ∈ Finset.Ioi i, log |t i - t j|) *
        rexp (-(poleBound n * ∑ i, externalField (t i))) ≤
        rexp B * rexp (-∑ i, √(t i)) := by
      rw [← exp_add, ← exp_add]
      exact exp_le_exp.2 (by simp only [B]; linarith)
    linarith [mul_le_mul_of_nonneg_right hE hR]
  calc _ ≤ ∫ t in S, rexp B * ∏ i, g (t i) :=
        integral_mono_ae (integrableOn_prod_sub_sq_mul_prod_exp_externalField hK1)
          (hG.const_mul _) hbound
    _ = _ := by rw [integral_const_mul, hGint]

/-- **The bound for `log Δ_K(ξ)`.** With `ξ = ζ(5)`, `K = 40 n`, `N = 3 n`, `h = 37 n`,
`λ = 37 / 40` and `ρ` the rational arcsine measure,
`log Δ_K(ξ) ≤ 2 h (h + 6N - K) log K + (-1329 λ / 200 - I(ρ)) K² + 18 h log K + 160 h`. -/
@[zeta5irr "lem_real_DeltaK"]
theorem log_aeval_gramDet_le {n : ℕ} (hn : 0 < n) :
    log (aeval zetaFive (gramDet n)) ≤
      2 * matrixOrder n * (matrixOrder n + 6 * innerDegree n - poleBound n) *
          log (poleBound n) +
        (-1329 * (orderRatio : ℝ) / 200 - logEnergy (rho.map ((↑) : ℝ → ℂ))) *
          (poleBound n : ℝ) ^ 2 +
        18 * matrixOrder n * log (poleBound n) + 160 * matrixOrder n := by
  have hK : (0 : ℝ) < poleBound n := by exact_mod_cast poleBound_pos hn
  have hΔ := (aeval_gramDet_le_integral_externalField hn).trans
    (mul_le_mul_of_nonneg_left (integral_prod_sub_sq_mul_prod_exp_externalField_le hn)
      (by positivity))
  have hlog := log_le_log (aeval_gramDet_pos n) hΔ
  rw [log_mul (by positivity) (by positivity), log_div (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_zpow, log_pow, log_mul (by positivity)
    (by positivity), log_exp, log_mul (by positivity) (by positivity), log_exp, log_pow]
    at hlog
  have hfac : 0 ≤ log ((matrixOrder n).factorial : ℝ) :=
    log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  have h4096 : log (4096 : ℝ) = 12 * log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_pow]
    norm_num
  have h652 : log (652 : ℝ) ≤ 10 * log 2 := by
    rw [show 10 * log 2 = log ((2 : ℝ) ^ 10) by rw [log_pow]; norm_num]
    exact log_le_log (by norm_num) (by norm_num)
  have hsqrt : √2 < 2 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  have hl2 := log_two_lt_d9
  have hc : (log 4096 + 12 + 120 + √2 + log 652) * matrixOrder n ≤ 160 * matrixOrder n :=
    mul_le_mul_of_nonneg_right (by norm_num at hl2; linarith) (by positivity)
  push_cast at hlog
  linarith

end Zeta5Irr
