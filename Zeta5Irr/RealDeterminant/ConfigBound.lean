/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Measure.Potential
public import Zeta5Irr.Measure.Energy
public import Zeta5Irr.RealDeterminant.SigmaReg
public import Zeta5Irr.RealDeterminant.ZeroMassEnergy
public import Zeta5Irr.RealDeterminant.ConfigIntegrable
public import Zeta5Irr.RealDeterminant.ConfigSelfEnergy
public import Zeta5Irr.RealDeterminant.ConfigError

/-!
# A bound for every configuration

Let `ε > 0`, let `t = (t_1, …, t_h) ∈ [0, ∞)^h` have pairwise distinct entries, and let
`W : [0, ∞) → ℝ` and `m ∈ ℝ` satisfy `2 U^ρ(x) - W(x) ≤ m` for every `x ≥ 0`, where `U^ρ` is the
logarithmic potential of the rational arcsine measure `ρ`. Then
`2 ∑_{i < j} log |t_i - t_j| - K ∑_i W(t_i) ≤ (λ m - I(ρ)) K² + 120 λ K² √ε - h log ε`.

The proof compares the regularised configuration measure `σ = σ_{t,ε}` with `ρ`. Both have
mass `λ`, so `ν = σ - ρ` has zero mass and nonpositive logarithmic energy. Expanding the energy
of `ν` bilinearly gives `I(σ) - 2 ∫ U^ρ dσ + I(ρ) ≤ 0`; the self- and mutual energies of the
circle measures bound `K² I(σ)` from below by `h log ε + 2 ∑_{i < j} log |t_i - t_j|`, and the
circle averages of `U^ρ` bound `∫ U^ρ dσ` from above by `K⁻¹ ∑_i U^ρ(t_i) + 60 h √ε / K`.

## Main results

* `Zeta5Irr.integral_integral_log_norm_sub_toSignedMeasure_sub`: the logarithmic energy of
  `μ₁ - μ₂` is `I(μ₁) - 2 ∫ U^{μ₂} dμ₁ + I(μ₂)` when the kernel is `(μ₁ + μ₂)^{⊗2}`-integrable.
* `Zeta5Irr.le_sq_mul_logEnergy_sigmaReg`:
  `h log ε + 2 ∑_{i < j} log |t_i - t_j| ≤ K² I(σ_{t,ε})` for an injective tuple `t`.
* `Zeta5Irr.integral_logPotential_rho_sigmaReg_le`:
  `∫ U^ρ dσ_{t,ε} ≤ K⁻¹ (∑_i U^ρ(t_i) + 60 h √ε)`.
* `Zeta5Irr.two_mul_sum_log_abs_sub_sub_le_of_eq`: the bound for every configuration, for any
  `K ≠ 0` and `h` with `h = λ K`.
* `Zeta5Irr.two_mul_sum_log_abs_sub_sub_le`: the bound for every configuration.

## Implementation notes

* The function `W` is taken on all of `ℝ`, the hypothesis `2 U^ρ(x) - W(x) ≤ m` being imposed
  only for `x ≥ 0`; its values on `(-∞, 0)` play no role.
* The measure `ρ` lives on `ℝ`; its potential and energy are those of its image
  `rho.map ((↑) : ℝ → ℂ)` on `ℂ`, and the points `t_i` are viewed in `ℂ`.
* The sum over `i < j` is written `∑ i, ∑ j ∈ Finset.Ioi i`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

open MeasureTheory VectorMeasure Real Set

open scoped ENNReal

namespace Zeta5Irr

/-- **Bilinear expansion of the logarithmic energy of a difference.** If `log |z - w|` is
integrable against `(μ₁ + μ₂) ⊗ (μ₁ + μ₂)`, then the logarithmic energy of `ν = μ₁ - μ₂` is
`I(μ₁) - 2 ∫ U^{μ₂} dμ₁ + I(μ₂)`. -/
theorem integral_integral_log_norm_sub_toSignedMeasure_sub (μ₁ μ₂ : Measure ℂ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hint : Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) ((μ₁ + μ₂).prod (μ₁ + μ₂))) :
    ∫ᵛ w, ∫ᵛ z, log ‖z - w‖ ∂<•(μ₁.toSignedMeasure - μ₂.toSignedMeasure)
        ∂<•(μ₁.toSignedMeasure - μ₂.toSignedMeasure) =
      logEnergy μ₁ - 2 * ∫ z, logPotential μ₂ z ∂μ₁ + logEnergy μ₂ := by
  set f : ℂ × ℂ → ℝ := fun p => log ‖p.1 - p.2‖
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add, integrable_add_measure,
    integrable_add_measure, integrable_add_measure] at hint
  obtain ⟨⟨h11, h12⟩, h21, h22⟩ := hint
  set ν := μ₁.toSignedMeasure - μ₂.toSignedMeasure
  set G : ℂ → ℝ := fun w => ∫ z, log ‖z - w‖ ∂μ₁ - ∫ z, log ‖z - w‖ ∂μ₂
  have hG : ∀ w, Integrable (fun z => log ‖z - w‖) μ₁ → Integrable (fun z => log ‖z - w‖) μ₂ →
      ∫ᵛ z, log ‖z - w‖ ∂<•ν = G w := fun w hw1 hw2 =>
    integral_toSignedMeasure_sub_toSignedMeasure μ₁ μ₂ hw1 hw2
  have hF1 : (fun w => ∫ᵛ z, log ‖z - w‖ ∂<•ν) =ᵐ[μ₁] G := by
    filter_upwards [h11.prod_left_ae, h21.prod_left_ae] with w hw1 hw2
    exact hG w hw1 hw2
  have hF2 : (fun w => ∫ᵛ z, log ‖z - w‖ ∂<•ν) =ᵐ[μ₂] G := by
    filter_upwards [h12.prod_left_ae, h22.prod_left_ae] with w hw1 hw2
    exact hG w hw1 hw2
  have hG1 : Integrable G μ₁ := h11.integral_prod_right.sub h21.integral_prod_right
  have hG2 : Integrable G μ₂ := h12.integral_prod_right.sub h22.integral_prod_right
  rw [integral_toSignedMeasure_sub_toSignedMeasure μ₁ μ₂ (hG1.congr hF1.symm)
      (hG2.congr hF2.symm), integral_congr_ae hF1, integral_congr_ae hF2,
    integral_sub h11.integral_prod_right h21.integral_prod_right,
    integral_sub h12.integral_prod_right h22.integral_prod_right]
  have hsymm : ∀ μ μ' : Measure ℂ, ∫ w, ∫ z, log ‖z - w‖ ∂μ ∂μ' =
      ∫ w, logPotential μ w ∂μ' := fun μ μ' => by
    simp only [logPotential, norm_sub_rev]
  have e11 : ∫ w, ∫ z, log ‖z - w‖ ∂μ₁ ∂μ₁ = logEnergy μ₁ := by
    rw [hsymm, logEnergy_eq_integral_integral h11]; rfl
  have e22 : ∫ w, ∫ z, log ‖z - w‖ ∂μ₂ ∂μ₂ = logEnergy μ₂ := by
    rw [hsymm, logEnergy_eq_integral_integral h22]; rfl
  have e21 : ∫ w, ∫ z, log ‖z - w‖ ∂μ₂ ∂μ₁ = ∫ z, logPotential μ₂ z ∂μ₁ := hsymm μ₂ μ₁
  have e12 : ∫ w, ∫ z, log ‖z - w‖ ∂μ₁ ∂μ₂ = ∫ z, logPotential μ₂ z ∂μ₁ := by
    rw [← integral_integral_swap (f := fun z w => log ‖z - w‖) h12]
    rfl
  rw [e11, e22, e21, e12]
  ring

/-- Twice the sum over `i < j` of a symmetric function is its sum over `i ≠ j`. -/
theorem sum_sum_ite_ne_eq_two_mul_sum_sum_Ioi {h : ℕ} (g : Fin h → Fin h → ℝ)
    (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, (if i = j then 0 else g i j) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have hsplit : ∀ i j, (if i = j then 0 else g i j) =
      (if i < j then g i j else 0) + (if j < i then g j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij.ne, hij, hij.not_gt]
    · simp
    · simp [hij.ne', hij, hij.not_gt, hg i j]
  have hIoi : ∀ i, ∑ j, (if i < j then g i j else 0) = ∑ j ∈ Finset.Ioi i, g i j := fun i => by
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then g j i else 0)]
  simp only [hIoi]
  ring

/-- `σ_{t,ε} ⊗ σ_{t,ε} = K⁻² ∑_{i,j} ϖ_{t_i,ε} ⊗ ϖ_{t_j,ε}`. -/
theorem sigmaReg_prod_sigmaReg {h : ℕ} (K : ℕ) (t : Fin h → ℂ) (ε : ℝ) :
    (sigmaReg K t ε).prod (sigmaReg K t ε) =
      ((K : ℝ≥0∞)⁻¹ * (K : ℝ≥0∞)⁻¹) •
        ∑ p : Fin h × Fin h, (circleUnif (t p.1) ε).prod (circleUnif (t p.2) ε) := by
  rw [sigmaReg, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← Measure.sum_fintype, Measure.prod_sum, Measure.sum_fintype]

/-- **The energy of the regularised configuration.** For an injective tuple `t` and `ε > 0`,
`K² I(σ_{t,ε}) ≥ h log ε + 2 ∑_{i < j} log |t_i - t_j|`. -/
theorem le_sq_mul_logEnergy_sigmaReg {h : ℕ} (K : ℕ) [NeZero K] {t : Fin h → ℂ}
    (ht : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    h * log ε + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, log ‖t i - t j‖ ≤
      (K : ℝ) ^ 2 * logEnergy (sigmaReg K t ε) := by
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hE : (K : ℝ) ^ 2 * logEnergy (sigmaReg K t ε) = ∑ i, ∑ j,
      ∫ p, log ‖p.1 - p.2‖ ∂(circleUnif (t i) ε).prod (circleUnif (t j) ε) := by
    rw [logEnergy, sigmaReg_prod_sigmaReg, integral_smul_measure,
      integral_finsetSum_measure fun p _ =>
        integrable_log_norm_sub_circleUnif_prod_circleUnif (t p.1) (t p.2) hε,
      ← Finset.univ_product_univ, Finset.sum_product]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    field_simp
  rw [hE]
  have hterm : ∀ i j, (if i = j then log ε else log ‖t i - t j‖) ≤
      ∫ p, log ‖p.1 - p.2‖ ∂(circleUnif (t i) ε).prod (circleUnif (t j) ε) := by
    intro i j
    split_ifs with hij
    · subst hij
      exact (integral_log_norm_sub_prod_circleUnif (t i) hε).2.ge
    · refine le_trans ?_ (log_max_norm_sub_le_integral_log_norm_sub_prod_circleUnif _ _ hε)
      exact log_le_log (norm_pos_iff.2 (sub_ne_zero.2 (ht.ne hij))) (le_max_left _ _)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    hterm i j)
  have hsplit : ∀ i j : Fin h, (if i = j then log ε else log ‖t i - t j‖) =
      (if i = j then log ε else 0) + (if i = j then 0 else log ‖t i - t j‖) := by
    intro i j; split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [sum_sum_ite_ne_eq_two_mul_sum_sum_Ioi (fun i j => log ‖t i - t j‖)
    fun i j => by rw [norm_sub_rev]]
  simp

/-- The rational arcsine measure `ρ`, viewed as a measure on `ℂ`. -/
local notation "ρℂ" => rho.map ((↑) : ℝ → ℂ)

/-- **The potential of `ρ` averaged against `σ_{t,ε}`.** For `ε > 0`,
`∫ U^ρ dσ_{t,ε} ≤ K⁻¹ ∑_i U^ρ(t_i) + 60 h √ε / K`. -/
theorem integral_logPotential_rho_sigmaReg_le {h : ℕ} (K : ℕ) [NeZero K] (t : Fin h → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z, logPotential ρℂ z ∂sigmaReg K t ε ≤
      (K : ℝ)⁻¹ * (∑ i, logPotential ρℂ (t i) + 60 * h * √ε) := by
  have hint : ∀ i, Integrable (logPotential ρℂ) (circleUnif (t i) ε) := fun i =>
    (integrable_log_norm_sub_circleUnif_prod ae_norm_le_two_rho_map (t i) hε).integral_prod_left
  rw [integral_sigmaReg K t ε hint, smul_eq_mul]
  have hK : (0 : ℝ) ≤ (K : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hK
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    integral_logPotential_rho_circleUnif_sub_le (t i) hε
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at this
  linarith

/-- **A bound for every configuration**, for general `K` and `h` with `h = λ K`. -/
theorem two_mul_sum_log_abs_sub_sub_le_of_eq {K h : ℕ} [NeZero K]
    (hKh : (h : ℝ) = orderRatio * K) {ε : ℝ} (hε : 0 < ε) {t : Fin h → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht : Function.Injective t) (W : ℝ → ℝ) (m : ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 2 * logPotential ρℂ x - W x ≤ m) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, log |t i - t j| - K * ∑ i, W (t i) ≤
      (orderRatio * m - logEnergy ρℂ) * K ^ 2 + 120 * orderRatio * K ^ 2 * √ε -
        h * log ε := by
  set tc : Fin h → ℂ := fun i => (t i : ℂ)
  set σ := sigmaReg K tc ε
  set ν : SignedMeasure ℂ := σ.toSignedMeasure - (ρℂ).toSignedMeasure
  have hKpos : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hint := integrable_log_norm_sub_sigmaReg_add_rho_prod K tc hε
  -- `ν` has total mass `h / K - λ = 0`
  have hν : ν univ = 0 := by
    simp only [ν, sub_apply,
      Measure.toSignedMeasure_apply_measurable MeasurableSet.univ, measureReal_def,
      σ, sigmaReg_univ, Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
      preimage_univ]
    rw [← measureReal_def, rho_real_univ, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, hKh]
    field_simp
    ring
  -- the hypothesis of the zero-mass energy lemma, from `|ν| ≤ σ + ρ`
  have hV : ν.variation ≤ σ + ρℂ := by
    refine (VectorMeasure.variation_sub_le).trans ?_
    rw [Measure.variation_toSignedMeasure, Measure.variation_toSignedMeasure]
  have : IsFiniteMeasure ν.variation := isFiniteMeasure_of_le (σ + ρℂ) hV
  have hlog : ∫⁻ p : ℂ × ℂ, (if p.1 = p.2 then ∞ else ‖log ‖p.1 - p.2‖‖ₑ)
      ∂(ν.variation.prod ν.variation) < ∞ := by
    refine (lintegral_mono' (Measure.prod_mono hV hV) le_rfl).trans_lt ?_
    have hdiag := sigmaReg_add_rho_prod_diagonal K tc hε.ne'
    rw [lintegral_congr_ae (g := fun p : ℂ × ℂ => ‖log ‖p.1 - p.2‖‖ₑ)]
    · exact hint.hasFiniteIntegral
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hdiag] with p hp
      have hp' : p.1 ≠ p.2 := hp
      simp [hp']
  have hE := integral_integral_log_norm_sub_nonpos ν hν hlog
  rw [integral_integral_log_norm_sub_toSignedMeasure_sub σ ρℂ hint] at hE
  -- the three estimates
  have hinj : Function.Injective tc := Complex.ofReal_injective.comp ht
  have h3 := le_sq_mul_logEnergy_sigmaReg K hinj hε
  have hnorm : ∀ i j, ‖tc i - tc j‖ = |t i - t j| := fun i j => by
    simp only [tc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at h3
  have h4 := integral_logPotential_rho_sigmaReg_le K tc hε
  have h5 : 2 * ∑ i, logPotential ρℂ (tc i) ≤ ∑ i, W (t i) + h * m := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hW (t i) (ht0 i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] at this
    linarith
  -- combine
  set A := logEnergy σ
  set B := ∫ z, logPotential ρℂ z ∂σ
  set U := ∑ i, logPotential ρℂ (tc i)
  have h4' : (K : ℝ) ^ 2 * B ≤ K * (U + 60 * h * √ε) := by
    have := (le_inv_mul_iff₀ hKpos).1 h4
    have := mul_le_mul_of_nonneg_left this hKpos.le
    linarith [show (K : ℝ) ^ 2 * B = K * (K * B) by ring]
  have hE' := mul_le_mul_of_nonneg_left hE (sq_nonneg (K : ℝ))
  have h5' := mul_le_mul_of_nonneg_left h5 hKpos.le
  have hh : (h : ℝ) * K = orderRatio * K ^ 2 := by rw [hKh]; ring
  have hhm : (h : ℝ) * K * m = orderRatio * K ^ 2 * m := by rw [hh]
  have hhs : (h : ℝ) * K * √ε = orderRatio * K ^ 2 * √ε := by rw [hh]
  linear_combination h3 + hE' + 2 * h4' + h5' + hhm + 120 * hhs

/-- **A bound for every configuration** (Fauzan, §10.2). Let `ε > 0`, let
`t = (t_1, …, t_h) ∈ [0, ∞)^h` have pairwise distinct entries, and let `W : ℝ → ℝ` and `m ∈ ℝ`
satisfy `2 U^ρ(x) - W(x) ≤ m` for every `x ≥ 0`. Then
`2 ∑_{i < j} log |t_i - t_j| - K ∑_i W(t_i) ≤ (λ m - I(ρ)) K² + 120 λ K² √ε - h log ε`,
where `K = 40 n`, `h = 37 n` and `λ = 37 / 40`. -/
@[zeta5irr "lem_config_bound"]
theorem two_mul_sum_log_abs_sub_sub_le {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {t : Fin (matrixOrder n) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht : Function.Injective t)
    (W : ℝ → ℝ) (m : ℝ) (hW : ∀ x : ℝ, 0 ≤ x → 2 * logPotential ρℂ x - W x ≤ m) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, log |t i - t j| - poleBound n * ∑ i, W (t i) ≤
      (orderRatio * m - logEnergy ρℂ) * (poleBound n : ℝ) ^ 2 +
        120 * orderRatio * (poleBound n : ℝ) ^ 2 * √ε - matrixOrder n * log ε := by
  have : NeZero (poleBound n) := ⟨(poleBound_pos hn).ne'⟩
  refine two_mul_sum_log_abs_sub_sub_le_of_eq ?_ hε ht0 ht W m hW
  simp only [matrixOrder, poleBound, orderRatio, Nat.cast_mul, Nat.cast_ofNat]
  push_cast
  ring

end Zeta5Irr
