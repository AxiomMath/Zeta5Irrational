/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VFormula
public import Zeta5Irr.RealDeterminant.Andreief
public import Zeta5Irr.RealDeterminant.RealWeightBound
public import Zeta5Irr.RealDeterminant.RealGamma652
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan

/-!
# The scaled multiple integral bounding `Δ_K(ξ)`

Let `ξ = ζ(5)`, `K = 40 n`, `N = 3 n`, `h = 37 n` and let `V` be the external field. Then
`Δ_K(ξ) ≤ K^{2h(h+6N-K)+16h} (4096 e¹²)^h / h! ·
  ∫_{(0,∞)^h} ∏_{i<j} (t_i - t_j)² ∏_i e^{-K V(t_i)} t_i^{-1/2} (1 + √t_i)⁵ dt`.

Starting from the Andréief expansion of `Δ_K(ξ)` as an `h`-fold integral over `(0, ∞)^h`,
one substitutes `y_i = K √t_i` in every coordinate. The Jacobian is `∏_i K / (2 √t_i)`, the
Vandermonde factor becomes `K^{2h(h-1)} ∏_{i<j} (t_i - t_j)²`, and each one-variable factor
`D_N(K²t)⁶ / D_K(K²t) · w(K√t) · K / (2√t)` is bounded by the scaled weight bound
`4096 e¹² K^{12N-2K+18} t^{-1/2} (1 + √t)⁵ e^{-K V(t)}`. All factors are nonnegative, so the
bound passes to the integral.

## Main results

* `Zeta5Irr.integral_pi_Ioi_eq_integral_comp_mul_sqrt`: the substitution `y_i = k √t_i` on
  `(0, ∞)^h`.
* `Zeta5Irr.sqrt_sub_two_le_externalField`: `√t - 2 ≤ V(t)` for `t > 0`.
* `Zeta5Irr.integrableOn_prod_sub_sq_mul_prod_exp_externalField`: the integrand of the scaled
  integral is integrable on `(0, ∞)^h`.
* `Zeta5Irr.aeval_gramDet_le_integral_externalField`: the bound for `Δ_K(ξ)`.

## Implementation notes

The integral is the Bochner integral over the box `Set.univ.pi fun _ => Set.Ioi 0` in
`Fin h → ℝ`. Since a Bochner integral of a non-integrable function is `0`, the statement is
only meaningful together with the integrability of its integrand, which is proved here from
the lower bound `V(t) ≥ √t - 2`: the integrand is dominated by a product of one-variable
functions `C (t^{-1/2} + t^{L-1/2}) e^{-√t}`. The substitution is performed in all
coordinates at once by the change of variables formula for the map `t ↦ (k √t_i)_i`, whose
derivative is diagonal, rather than one variable at a time through Tonelli's theorem. The
power of `K` is an integer power, as in the scaled weight bound.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (The Gram integral and scaling).
-/

@[expose] public section

open Real MeasureTheory Set Polynomial

namespace Zeta5Irr

/-- A lower bound for the external field: `√t - 2 ≤ V(t)` for every `t > 0`. -/
theorem sqrt_sub_two_le_externalField {t : ℝ} (ht : 0 < t) : √t - 2 ≤ externalField t := by
  rw [externalField_eq ht]
  set a : ℝ := (innerRatio : ℝ)
  have ha : a = 3 / 40 := by simp [a, innerRatio]
  have hs : 0 < √t := sqrt_pos.2 ht
  have h1 : 0 ≤ log (1 + t) := log_nonneg (by linarith)
  have h2 : log (t + a ^ 2) ≤ 2 * √t := by
    calc log (t + a ^ 2) ≤ log ((1 + √t) ^ 2) := by
          apply log_le_log (by positivity)
          rw [add_sq, sq_sqrt ht.le, ha]; nlinarith
      _ = 2 * log (1 + √t) := by rw [log_pow]; norm_num
      _ ≤ 2 * √t := by
          have := log_le_sub_one_of_pos (show 0 < 1 + √t by positivity)
          linarith
  have h3 : 0 ≤ arctan (1 / √t) := arctan_nonneg.2 (by positivity)
  have h4 : arctan (a / √t) ≤ a / √t := arctan_le_self (by rw [ha]; positivity)
  have h5 : 2 * √t * (a / √t) = 2 * a := by field_simp
  have hpi := pi_gt_three
  nlinarith

/-- For nonnegative `t_1, …, t_h`, `∏_{i<j} (t_i - t_j)² ≤ ∏_i (1 + t_i)^{4h}`. -/
theorem prod_prod_Ioi_sub_sq_le_prod_one_add_pow {h : ℕ} {t : Fin h → ℝ}
    (ht : ∀ i, 0 ≤ t i) :
    ∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2 ≤ ∏ i, (1 + t i) ^ (4 * h) := by
  calc ∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2
      ≤ ∏ i, ∏ j ∈ Finset.Ioi i, ((1 + t i) ^ 2 * (1 + t j) ^ 2) := by
        refine Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _)
          fun i _ => Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) fun j _ => ?_
        rw [← mul_pow]
        exact sq_le_sq' (by nlinarith [ht i, ht j]) (by nlinarith [ht i, ht j])
    _ ≤ ∏ i, ∏ j, ((1 + t i) ^ 2 * (1 + t j) ^ 2) := by
        refine Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
          fun i _ => Finset.prod_mono_set_of_one_le₀ (fun j => ?_) (Finset.subset_univ _)
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [ht i]))
          (one_le_pow₀ (by linarith [ht j]))
    _ = ∏ i, (1 + t i) ^ (4 * h) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Finset.prod_pow, ← pow_mul]
        rw [← pow_add, show 2 * h + 2 * h = 4 * h by ring]

/-- For `k ≥ 1`, the function
`t ↦ ∏_{i<j} (t_i - t_j)² ∏_i e^{-k V(t_i)} t_i^{-1/2} (1 + √t_i)⁵` is integrable on
`(0, ∞)^h`. -/
theorem integrableOn_prod_sub_sq_mul_prod_exp_externalField {h : ℕ} {k : ℝ} (hk : 1 ≤ k) :
    IntegrableOn (fun t : Fin h → ℝ => (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
      ∏ i, rexp (-(k * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) * (1 + √(t i)) ^ 5)
      (univ.pi fun _ => Ioi 0) := by
  set L : ℕ := 4 * h + 5
  set C : ℝ := rexp (2 * k) * 32 * 2 ^ L
  let f : ℝ → ℝ := fun s => C * (s ^ (-(1 / 2 : ℝ)) * rexp (-1 * s ^ (1 / 2 : ℝ)) +
    s ^ ((L : ℝ) - 1 / 2) * rexp (-1 * s ^ (1 / 2 : ℝ)))
  have hf : IntegrableOn f (Ioi 0) :=
    ((integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)).add
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (by linarith [(L.cast_nonneg : (0:ℝ) ≤ L)]) (by norm_num) (by norm_num))).const_mul C
  have hF : Integrable (fun t : Fin h → ℝ => ∏ i, f (t i))
      (volume.restrict (univ.pi fun _ => Ioi (0:ℝ))) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun _ => hf
  -- the closed form of the external field is measurable
  let Vc : ℝ → ℝ := fun t => log (1 + t) - 6 * (innerRatio : ℝ) *
    log (t + (innerRatio : ℝ) ^ 2) - 2 + 12 * (innerRatio : ℝ) +
      2 * √t * (π + arctan (1 / √t) - 6 * arctan ((innerRatio : ℝ) / √t))
  have hVc : Measurable Vc := by fun_prop
  have hS : MeasurableSet (univ.pi fun _ : Fin h => Ioi (0:ℝ)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  refine hF.mono' ?_ (ae_restrict_of_forall_mem hS fun t ht => ?_)
  · refine AEStronglyMeasurable.congr (f := fun t : Fin h → ℝ =>
      (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
      ∏ i, rexp (-(k * Vc (t i))) * t i ^ (-(1 / 2 : ℝ)) * (1 + √(t i)) ^ 5) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.mul ?_ ?_
      · exact Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => by
          fun_prop
      · exact Finset.measurable_prod _ fun i _ => by
          have : Measurable fun t : Fin h → ℝ => Vc (t i) := hVc.comp (measurable_pi_apply i)
          fun_prop
    · refine ae_restrict_of_forall_mem hS fun t ht => ?_
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      simp only [Vc, ← externalField_eq (ht i (mem_univ i))]
  · have ht0 : ∀ i, 0 < t i := fun i => ht i (mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity))]
    refine (mul_le_mul_of_nonneg_right
      (prod_prod_Ioi_sub_sq_le_prod_one_add_pow fun i => (ht0 i).le)
      (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity)).trans ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => by have := ht0 i; positivity) fun i _ => ?_
    set s := t i
    have hs : 0 < s := ht0 i
    have hsq : s ^ (1 / 2 : ℝ) = √s := (sqrt_eq_rpow s).symm
    have hV := sqrt_sub_two_le_externalField hs
    have hsq0 : 0 ≤ √s := sqrt_nonneg s
    have hexp : rexp (-(k * externalField s)) ≤ rexp (2 * k) * rexp (-1 * s ^ (1 / 2 : ℝ)) := by
      rw [← exp_add, hsq]
      apply exp_le_exp.2
      nlinarith
    have h1s : (1 + √s) ^ 5 ≤ 32 * (1 + s) ^ 5 := by
      have : 1 + √s ≤ 2 * (1 + s) := by
        nlinarith [sq_sqrt hs.le]
      calc (1 + √s) ^ 5 ≤ (2 * (1 + s)) ^ 5 := pow_le_pow_left₀ (by positivity) this 5
        _ = _ := by ring
    have hL := one_add_pow_le_two_pow_mul_one_add_pow L hs.le
    have hpow : s ^ (L : ℕ) * s ^ (-(1 / 2 : ℝ)) = s ^ ((L : ℝ) - 1 / 2) := by
      rw [← rpow_natCast, ← rpow_add hs]; ring_nf
    have hr : 0 < s ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos hs _
    have he : 0 < rexp (-1 * s ^ (1 / 2 : ℝ)) := exp_pos _
    simp only [f, C]
    rw [← hpow]
    calc (1 + s) ^ (4 * h) * (rexp (-(k * externalField s)) * s ^ (-(1 / 2 : ℝ)) *
          (1 + √s) ^ 5)
        ≤ (1 + s) ^ (4 * h) * (rexp (2 * k) * rexp (-1 * s ^ (1 / 2 : ℝ)) *
          s ^ (-(1 / 2 : ℝ)) * (32 * (1 + s) ^ 5)) := by gcongr
      _ = rexp (2 * k) * 32 * ((1 + s) ^ L * s ^ (-(1 / 2 : ℝ)) *
          rexp (-1 * s ^ (1 / 2 : ℝ))) := by simp only [L]; ring
      _ ≤ rexp (2 * k) * 32 * ((2 ^ L * (1 + s ^ L)) * s ^ (-(1 / 2 : ℝ)) *
          rexp (-1 * s ^ (1 / 2 : ℝ))) := by gcongr
      _ = _ := by ring

/-- **Substitution `y_i = k √t_i` on `(0, ∞)^h`.** For `k > 0` and any `g`,
`∫_{(0,∞)^h} g(y) dy = ∫_{(0,∞)^h} (∏_i k / (2 √t_i)) g((k √t_i)_i) dt`. -/
theorem integral_pi_Ioi_eq_integral_comp_mul_sqrt {h : ℕ} {k : ℝ} (hk : 0 < k)
    (g : (Fin h → ℝ) → ℝ) :
    ∫ y in univ.pi fun _ : Fin h => Ioi (0 : ℝ), g y =
      ∫ t in univ.pi fun _ : Fin h => Ioi (0 : ℝ),
        (∏ i, k / (2 * √(t i))) * g fun i => k * √(t i) := by
  set S := univ.pi fun _ : Fin h => Ioi (0 : ℝ)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  let Φ : (Fin h → ℝ) → (Fin h → ℝ) := fun t i => k * √(t i)
  let d : (Fin h → ℝ) → Fin h → ℝ := fun t i => k / (2 * √(t i))
  let Φ' : (Fin h → ℝ) → (Fin h → ℝ) →L[ℝ] (Fin h → ℝ) := fun t =>
    ContinuousLinearMap.pi fun i => d t i • ContinuousLinearMap.proj i
  have hΦ' : ∀ t ∈ S, HasFDerivWithinAt Φ (Φ' t) S t := by
    intro t ht
    refine HasFDerivAt.hasFDerivWithinAt ?_
    refine hasFDerivAt_pi.2 fun i => ?_
    have hti : t i ≠ 0 := (ht i (mem_univ i)).ne'
    rw [show d t i = k * (1 / (2 * √(t i))) by simp only [d]; ring]
    exact HasDerivAt.comp_hasFDerivAt (f := fun s : Fin h → ℝ => s i) t
      ((hasDerivAt_sqrt hti).const_mul k)
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin h => ℝ) i t)
  have hinj : InjOn Φ S := by
    intro s hs t ht hst
    funext i
    have h := congrFun hst i
    simp only [Φ, mul_right_inj' hk.ne'] at h
    exact (sqrt_inj (hs i (mem_univ i)).le (ht i (mem_univ i)).le).1 h
  have himg : Φ '' S = S := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩ i _
      exact mul_pos hk (sqrt_pos.2 (ht i (mem_univ i)))
    · intro hy
      refine ⟨fun i => (y i / k) ^ 2, fun i _ => by
        have := hy i (mem_univ i); simp only [mem_Ioi] at this ⊢; positivity, ?_⟩
      funext i
      have := hy i (mem_univ i)
      simp only [mem_Ioi] at this
      simp only [Φ]
      rw [sqrt_sq (by positivity)]
      field_simp
  have hdet : ∀ t, (Φ' t).det = ∏ i, d t i := by
    intro t
    have : (Φ' t : (Fin h → ℝ) →ₗ[ℝ] (Fin h → ℝ)) =
        Matrix.toLin' (Matrix.diagonal (d t)) := by
      ext v i
      simp [Φ', Matrix.mulVec_diagonal]
    rw [ContinuousLinearMap.det, this, LinearMap.det_toLin', Matrix.det_diagonal]
  rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hS hΦ' hinj, himg]
  refine setIntegral_congr_fun hS fun t ht => ?_
  rw [hdet, smul_eq_mul, abs_of_nonneg]
  exact Finset.prod_nonneg fun i _ => by
    have := ht i (mem_univ i); simp only [mem_Ioi] at this; simp only [d]; positivity

/-- There are `h (h - 1) / 2` pairs `i < j` in `Fin h`. -/
theorem sum_card_Ioi_mul_two (h : ℕ) :
    (∑ i : Fin h, (Finset.Ioi i).card) * 2 = h * (h - 1) := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i), Finset.sum_range_reflect (fun i => i) h,
    Finset.sum_range_id_mul_two]

/-- The pointwise bound behind the scaled integral: after the substitution `y_i = K √t_i`,
the Jacobian times the Andréief integrand is at most
`K^{2h(h+6N-K)+16h} (4096 e¹²)^h ∏_{i<j} (t_i - t_j)² ∏_i e^{-K V(t_i)} t_i^{-1/2}
(1 + √t_i)⁵`. -/
theorem prod_div_sqrt_mul_prod_le {n : ℕ} (hn : 0 < n) {t : Fin (matrixOrder n) → ℝ}
    (ht : ∀ i, 0 < t i) :
    (∏ i, (poleBound n : ℝ) / (2 * √(t i))) *
      ((∏ i, ∏ j ∈ Finset.Ioi i,
          ((poleBound n * √(t i)) ^ 2 - (poleBound n * √(t j)) ^ 2) ^ 2) *
        ∏ i, (poleProductRange (innerDegree n) ℝ).eval ((poleBound n * √(t i)) ^ 2) ^ 6 /
          (poleProductRange (poleBound n) ℝ).eval ((poleBound n * √(t i)) ^ 2) *
            weight (poleBound n * √(t i))) ≤
      (poleBound n : ℝ) ^ (2 * (matrixOrder n : ℤ) * (matrixOrder n + 6 * innerDegree n -
          poleBound n) + 16 * matrixOrder n) * (4096 * rexp 12) ^ matrixOrder n *
        ((∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
          ∏ i, rexp (-(poleBound n * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) *
            (1 + √(t i)) ^ 5) := by
  set K : ℕ := poleBound n
  set N : ℕ := innerDegree n
  have hK : (0 : ℝ) < K := by exact_mod_cast poleBound_pos hn
  have hsq : ∀ i, ((K : ℝ) * √(t i)) ^ 2 = (K : ℝ) ^ 2 * t i := fun i => by
    rw [mul_pow, sq_sqrt (ht i).le]
  simp only [hsq]
  have hV : ∏ i, ∏ j ∈ Finset.Ioi i, ((K : ℝ) ^ 2 * t i - (K : ℝ) ^ 2 * t j) ^ 2 =
      (K : ℝ) ^ (4 * ∑ i : Fin (matrixOrder n), (Finset.Ioi i).card) *
        ∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2 := by
    have : ∀ i j, ((K : ℝ) ^ 2 * t i - (K : ℝ) ^ 2 * t j) ^ 2 =
        (K : ℝ) ^ 4 * (t i - t j) ^ 2 := fun i j => by ring
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      ← pow_mul]
    rw [Finset.mul_sum]
  set e : ℤ := 12 * (N : ℤ) - 2 * K + 18
  set B : ℝ := 4096 * rexp 12 * (K : ℝ) ^ e
  have hW : (∏ i, (K : ℝ) / (2 * √(t i))) *
      ∏ i, (poleProductRange N ℝ).eval ((K : ℝ) ^ 2 * t i) ^ 6 /
        (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t i) * weight (K * √(t i)) ≤
      B ^ (matrixOrder n) * ∏ i, rexp (-(K * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) *
        (1 + √(t i)) ^ 5 := by
    rw [← Finset.prod_mul_distrib]
    rw [show B ^ matrixOrder n = ∏ _i : Fin (matrixOrder n), B by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
    · have hti := ht i
      have hp : 0 < (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t i) := by
        rw [eval_poleProductRange]
        exact Finset.prod_pos fun _ _ => by positivity
      have hw := weight_pos (mul_pos hK (sqrt_pos.2 hti))
      positivity
    · calc (K : ℝ) / (2 * √(t i)) * ((poleProductRange N ℝ).eval ((K : ℝ) ^ 2 * t i) ^ 6 /
            (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t i) * weight (K * √(t i)))
          = (poleProductRange N ℝ).eval ((K : ℝ) ^ 2 * t i) ^ 6 /
            (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t i) * weight (K * √(t i)) *
              (K / (2 * √(t i))) := by ring
        _ ≤ _ := eval_poleProductRange_innerDegree_pow_div_mul_weight_le hn (ht i)
        _ = _ := by simp only [B]; ring
  have hexp : (K : ℝ) ^ (2 * ((matrixOrder n) : ℤ) * ((matrixOrder n) + 6 * N - K) +
      16 * (matrixOrder n)) * (4096 * rexp 12) ^ (matrixOrder n) =
      (K : ℝ) ^ (4 * ∑ i : Fin (matrixOrder n), (Finset.Ioi i).card) * B ^ (matrixOrder n) := by
    have hP := sum_card_Ioi_mul_two (matrixOrder n)
    have hh : 1 ≤ (matrixOrder n) := matrixOrder_pos hn
    have hPz : (∑ i : Fin (matrixOrder n), ((Finset.Ioi i).card : ℤ)) * 2 =
        (matrixOrder n) * ((matrixOrder n) - 1) := by
      have := congrArg (fun m : ℕ => (m : ℤ)) hP
      push_cast [Nat.cast_sub hh] at this
      exact this
    have hB : B ^ matrixOrder n = (4096 * rexp 12) ^ matrixOrder n *
        (K : ℝ) ^ (e * (matrixOrder n : ℤ)) := by
      simp only [B]
      rw [mul_pow, ← zpow_natCast ((K : ℝ) ^ e), ← zpow_mul]
    have hz : 2 * ((matrixOrder n) : ℤ) * ((matrixOrder n) + 6 * N - K) + 16 * (matrixOrder n) =
        ((4 * ∑ i : Fin (matrixOrder n), (Finset.Ioi i).card : ℕ) : ℤ) +
          e * (matrixOrder n) := by
      push_cast
      simp only [e]
      linear_combination (-2) * hPz
    rw [hB, ← zpow_natCast (K : ℝ) (4 * _), mul_left_comm, ← zpow_add₀ hK.ne', ← hz,
      mul_comm]
  rw [hexp]
  calc (∏ i, (K : ℝ) / (2 * √(t i))) * ((∏ i, ∏ j ∈ Finset.Ioi i,
        ((K : ℝ) ^ 2 * t i - (K : ℝ) ^ 2 * t j) ^ 2) *
        ∏ i, (poleProductRange N ℝ).eval ((K : ℝ) ^ 2 * t i) ^ 6 /
          (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t i) * weight (K * √(t i)))
      = (K : ℝ) ^ (4 * ∑ i : Fin (matrixOrder n), (Finset.Ioi i).card) *
        (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) * ((∏ i, (K : ℝ) / (2 * √(t i))) *
        ∏ i, (poleProductRange N ℝ).eval ((K : ℝ) ^ 2 * t i) ^ 6 /
          (poleProductRange K ℝ).eval ((K : ℝ) ^ 2 * t i) * weight (K * √(t i))) := by
        rw [hV]; ring
    _ ≤ (K : ℝ) ^ (4 * ∑ i : Fin (matrixOrder n), (Finset.Ioi i).card) *
        (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) * (B ^ (matrixOrder n) *
          ∏ i, rexp (-(K * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) *
            (1 + √(t i)) ^ 5) := by
        gcongr
    _ = _ := by ring

/-- **The scaled multiple integral.** With `ξ = ζ(5)`, `K = 40 n`, `N = 3 n`, `h = 37 n` and
`V` the external field,
`Δ_K(ξ) ≤ K^{2h(h+6N-K)+16h} (4096 e¹²)^h / h! ·
  ∫_{(0,∞)^h} ∏_{i<j} (t_i - t_j)² ∏_i e^{-K V(t_i)} t_i^{-1/2} (1 + √t_i)⁵ dt`. -/
@[zeta5irr "lem_real_scaled_integral"]
theorem aeval_gramDet_le_integral_externalField {n : ℕ} (hn : 0 < n) :
    aeval zetaFive (gramDet n) ≤
      (poleBound n : ℝ) ^ (2 * (matrixOrder n : ℤ) * (matrixOrder n + 6 * innerDegree n -
          poleBound n) + 16 * matrixOrder n) * (4096 * rexp 12) ^ matrixOrder n /
          (matrixOrder n).factorial *
        ∫ t in univ.pi fun _ : Fin (matrixOrder n) => Ioi (0 : ℝ),
          (∏ i, ∏ j ∈ Finset.Ioi i, (t i - t j) ^ 2) *
            ∏ i, rexp (-(poleBound n * externalField (t i))) * t i ^ (-(1 / 2 : ℝ)) *
              (1 + √(t i)) ^ 5 := by
  have hK1 : (1 : ℝ) ≤ poleBound n := by exact_mod_cast poleBound_pos hn
  have hK : (0 : ℝ) < poleBound n := by linarith
  have hS : MeasurableSet (univ.pi fun _ : Fin (matrixOrder n) => Ioi (0 : ℝ)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  rw [aeval_gramDet_eq_integral, integral_pi_Ioi_eq_integral_comp_mul_sqrt hK]
  set c : ℝ := (poleBound n : ℝ) ^ (2 * (matrixOrder n : ℤ) * (matrixOrder n +
    6 * innerDegree n - poleBound n) + 16 * matrixOrder n) * (4096 * rexp 12) ^ matrixOrder n
  have hle := integral_mono_of_nonneg (ae_restrict_of_forall_mem hS fun t ht => ?_)
    ((integrableOn_prod_sub_sq_mul_prod_exp_externalField (h := matrixOrder n) hK1).const_mul c)
    (ae_restrict_of_forall_mem hS fun t ht =>
      prod_div_sqrt_mul_prod_le hn fun i => ht i (mem_univ i))
  · rw [integral_const_mul] at hle
    calc _ ≤ ((matrixOrder n).factorial : ℝ)⁻¹ * (c * _) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by ring
  · have ht0 : ∀ i, 0 < t i := fun i => ht i (mem_univ i)
    refine mul_nonneg (Finset.prod_nonneg fun i _ => by have := ht0 i; positivity)
      (mul_nonneg (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _)
        (Finset.prod_nonneg fun i _ => ?_))
    have hy : 0 < (poleBound n : ℝ) * √(t i) := mul_pos hK (sqrt_pos.2 (ht0 i))
    have hp : 0 < (poleProductRange (poleBound n) ℝ).eval
        (((poleBound n : ℝ) * √(t i)) ^ 2) := by
      rw [eval_poleProductRange]
      exact Finset.prod_pos fun _ _ => by positivity
    have hw := weight_pos hy
    positivity

end Zeta5Irr
