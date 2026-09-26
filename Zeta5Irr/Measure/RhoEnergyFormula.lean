/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Energy
public import Zeta5Irr.Measure.RhoPartial
public import Zeta5Irr.Measure.RhoMutual

/-!
# The energy of the rational arcsine measure `ρ`

For `ρ = ∑_{j=1}^{16} cⱼ ω_{[aⱼ,bⱼ]}` with partial sums `Sⱼ = ∑_{i ≤ j} cᵢ`, the logarithmic
energy is
`I(ρ) = ∑_{j=1}^{16} (Sⱼ² - S_{j-1}²) log ((bⱼ - aⱼ)/4)`.

Expanding `ρ ⊗ ρ` into the `256` products `c_k c_j ω_{[a_k,b_k]} ⊗ ω_{[a_j,b_j]}`, each mutual
energy is `log ((b_m - a_m)/4)` with `m = max k j`, by the nesting of the intervals and the
symmetry of `log |t - u|`. Collecting the pairs with `max k j = m` gives the coefficient
`c_m² + 2 c_m S_{m-1} = S_m² - S_{m-1}²`.

## Main results

* `Zeta5Irr.integrable_log_abs_sub_arcsineMeasure_prod`: for nested intervals
  `[c, d] ⊆ [a, b]`, `(t, u) ↦ log |t - u|` is integrable against `ω_{[c,d]} ⊗ ω_{[a,b]}`.
* `Zeta5Irr.sum_sum_mul_mul_max`: `∑_{k,j} c_k c_j L_{max k j} = ∑_m (S_{≤m}² - S_{<m}²) L_m`.
* `Zeta5Irr.integrable_log_norm_sub_rho`, `Zeta5Irr.rho_map_prod_diagonal`: the energy integral
  of `ρ` converges absolutely, and the diagonal is `ρ ⊗ ρ`-null.
* `Zeta5Irr.prod_setOf_fst_eq_snd_eq_zero`: the diagonal is `μ ⊗ ν`-null when `ν` has no
  atoms.
* `Zeta5Irr.logEnergy_rho`: `I(ρ) = ∑ⱼ (Sⱼ² - S_{j-1}²) log ((bⱼ - aⱼ)/4)`.

## Implementation notes

* `ρ` is a measure on `ℝ` and the energy is defined for measures on `ℂ`, so `I(ρ)` is the
  energy of the image of `ρ` under `ℝ → ℂ`.
* The energy is a Bochner integral, a junk value when the integrand is not integrable. The
  integrability of `log |t - u|` for `ρ ⊗ ρ` and the nullity of the diagonal are proved
  alongside the formula; together they say that the source integral converges absolutely.
* The rows are indexed by `j : Fin 16` from `0`, so `Sⱼ` and `S_{j-1}` of the source are
  `rhoPartial (j + 1)` and `rhoPartial j`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

/-- The arcsine measure `ω_{[a,b]}` is a finite measure; it is the zero measure when `b ≤ a`. -/
instance isFiniteMeasure_arcsineMeasure (a b : ℝ) : IsFiniteMeasure (arcsineMeasure a b) := by
  by_cases hab : a < b
  · have := isProbabilityMeasure_arcsineMeasure hab
    infer_instance
  · have : arcsineMeasure a b = 0 := by
      rw [arcsineMeasure, show arcsinePDF a b = 0 from funext fun u ↦
        arcsinePDF_of_notMem fun hu ↦ hab (hu.1.trans hu.2), withDensity_zero]
    rw [this]
    infer_instance

/-- For `a < b`, `a ≤ c < d ≤ b`, `(t, u) ↦ log |t - u|` is integrable against
`ω_{[c,d]} ⊗ ω_{[a,b]}`. -/
theorem integrable_log_abs_sub_arcsineMeasure_prod {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    Integrable (fun p : ℝ × ℝ ↦ Real.log |p.1 - p.2|)
      ((arcsineMeasure c d).prod (arcsineMeasure a b)) := by
  have := isProbabilityMeasure_arcsineMeasure hcd
  have := isProbabilityMeasure_arcsineMeasure hab
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ Real.log |p.1 - p.2|)
      ((arcsineMeasure c d).prod (arcsineMeasure a b)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ ↦ Real.log |p.1 - p.2|).aestronglyMeasurable
  have hae : ∀ᵐ t ∂arcsineMeasure c d, t ∈ Icc a b :=
    (ae_mem_Icc_arcsineMeasure c d).mono fun t ht ↦ ⟨hac.trans ht.1, ht.2.trans hdb⟩
  set M : ℝ := max (Real.log (b - a)) 0
  have hbound : ∀ t ∈ Icc a b,
      ∫ u, ‖Real.log |t - u|‖ ∂arcsineMeasure a b ≤ 2 * M - Real.log ((b - a) / 4) := by
    intro t ht
    have hi := integrable_log_abs_sub_arcsineMeasure hab t
    have hsub : ∫ u, (2 * M - Real.log |t - u|) ∂arcsineMeasure a b =
        2 * M - Real.log ((b - a) / 4) := by
      rw [integral_sub (integrable_const _) hi, integral_const,
        integral_log_abs_sub_arcsineMeasure hab ht]
      simp
    rw [← hsub]
    refine integral_mono_ae hi.norm ((integrable_const _).sub hi) ?_
    filter_upwards [ae_mem_Icc_arcsineMeasure a b] with u hu
    have hle : Real.log |t - u| ≤ M := by
      rcases eq_or_ne |t - u| 0 with h | h
      · rw [h, Real.log_zero]; exact le_max_right _ _
      · refine (Real.log_le_log ((abs_nonneg _).lt_of_ne' h) ?_).trans (le_max_left _ _)
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
    have hM : 0 ≤ M := le_max_right _ _
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine (integrable_prod_iff hmeas).2
    ⟨.of_forall fun t ↦ integrable_log_abs_sub_arcsineMeasure hab t, ?_⟩
  refine Integrable.mono' (integrable_const (2 * M - Real.log ((b - a) / 4)))
    hmeas.norm.integral_prod_right' (hae.mono fun t ht ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  exact hbound t ht

/-- Weighted double sums over a kernel depending only on `max k j`: for weights `cᵢ` and values
`Lₘ` indexed by `Fin n`, `∑_{k,j} c_k c_j L_{max k j} = ∑_m (S_{≤m}² - S_{<m}²) L_m`, where
`S_{≤m}` and `S_{<m}` are the sums of `cᵢ` over `i ≤ m` and over `i < m`. -/
theorem sum_sum_mul_mul_max {R : Type*} [CommRing R] {n : ℕ} (c L : Fin n → R) :
    ∑ k, ∑ j, c k * c j * L (max k j) =
      ∑ m, ((∑ i ∈ Finset.univ.filter (· ≤ m), c i) ^ 2 -
        (∑ i ∈ Finset.univ.filter (· < m), c i) ^ 2) * L m := by
  have key : ∀ m k j : Fin n, (if k ≤ m then c k else 0) * (if j ≤ m then c j else 0) -
      (if k < m then c k else 0) * (if j < m then c j else 0) =
        if max k j = m then c k * c j else 0 := by
    intro m k j
    simp only [max_def, apply_ite (fun x : Fin n ↦ x = m), Fin.le_def, Fin.lt_def, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | ring
  calc ∑ k, ∑ j, c k * c j * L (max k j)
      = ∑ k, ∑ j, ∑ m, (if max k j = m then c k * c j else 0) * L m := by
        simp [ite_mul]
    _ = ∑ m, (∑ k, ∑ j, if max k j = m then c k * c j else 0) * L m := by
        simp_rw [Finset.sum_mul]
        conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
        exact Finset.sum_comm
    _ = _ := by
        simp_rw [sq, Finset.sum_filter, Finset.sum_mul_sum, ← Finset.sum_sub_distrib, key]

/-- For all `k, j`, `(t, u) ↦ log |t - u|` is integrable against
`ω_{[a_k,b_k]} ⊗ ω_{[a_j,b_j]}`. -/
theorem integrable_log_abs_sub_arcsineMeasure_rho (k j : Fin 16) :
    Integrable (fun p : ℝ × ℝ ↦ Real.log |p.1 - p.2|)
      ((arcsineMeasure (rhoA k) (rhoB k)).prod (arcsineMeasure (rhoA j) (rhoB j))) := by
  have hlt := rhoA_lt_rhoB_real
  rcases le_total k j with hkj | hjk
  · exact integrable_log_abs_sub_arcsineMeasure_prod (hlt j) (hlt k)
      (by exact_mod_cast strictAnti_rhoA.antitone hkj)
      (by exact_mod_cast strictMono_rhoB.monotone hkj)
  · have := (integrable_log_abs_sub_arcsineMeasure_prod (hlt k) (hlt j)
      (by exact_mod_cast strictAnti_rhoA.antitone hjk)
      (by exact_mod_cast strictMono_rhoB.monotone hjk)).swap
    refine this.congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, abs_sub_comm]

/-- For all `k, j`, `∬ log |t - u| dω_{[a_k,b_k]}(t) dω_{[a_j,b_j]}(u) = log ((b_m - a_m)/4)`
with `m = max k j`. -/
theorem integral_log_abs_sub_arcsineMeasure_rho (k j : Fin 16) :
    ∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂(arcsineMeasure (rhoA k) (rhoB k)).prod (arcsineMeasure (rhoA j) (rhoB j)) =
      Real.log (((rhoB (max k j) : ℝ) - rhoA (max k j)) / 4) := by
  rcases le_total k j with hkj | hjk
  · rw [integral_prod _ (integrable_log_abs_sub_arcsineMeasure_rho k j), max_eq_right hkj,
      integral_integral_log_abs_sub_rho hkj]
  · rw [← integral_prod_swap, max_eq_left hjk]
    simp_rw [Prod.fst_swap, Prod.snd_swap, abs_sub_comm]
    rw [integral_prod _ (integrable_log_abs_sub_arcsineMeasure_rho j k),
      integral_integral_log_abs_sub_rho hjk]

/-- The measure `ρ ⊗ ρ` on `ℝ × ℝ` is the sum of `c_k c_j ω_{[a_k,b_k]} ⊗ ω_{[a_j,b_j]}`. -/
theorem rho_prod_rho : rho.prod rho = ∑ p : Fin 16 × Fin 16,
    (ENNReal.ofReal (rhoC p.1) * ENNReal.ofReal (rhoC p.2)) •
      (arcsineMeasure (rhoA p.1) (rhoB p.1)).prod (arcsineMeasure (rhoA p.2) (rhoB p.2)) := by
  have h (μ ν : Fin 16 → Measure ℝ) [∀ i, SFinite (ν i)] :
      (∑ i, μ i).prod (∑ j, ν j) = ∑ p : Fin 16 × Fin 16, (μ p.1).prod (ν p.2) := by
    rw [← Measure.sum_fintype, ← Measure.sum_fintype, Measure.prod_sum, Measure.sum_fintype]
  rw [rho, h]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, mul_comm]

/-- `(t, u) ↦ log |t - u|` is integrable against `ρ ⊗ ρ`. -/
theorem integrable_log_abs_sub_rho_prod :
    Integrable (fun p : ℝ × ℝ ↦ Real.log |p.1 - p.2|) (rho.prod rho) := by
  rw [rho_prod_rho, integrable_finsetSum_measure]
  exact fun p _ ↦ (integrable_log_abs_sub_arcsineMeasure_rho p.1 p.2).smul_measure
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- The double integral of `log |t - u|` against `ρ ⊗ ρ` on `ℝ × ℝ` is
`∑ⱼ (Sⱼ² - S_{j-1}²) log ((bⱼ - aⱼ)/4)`. -/
theorem integral_log_abs_sub_rho_prod :
    ∫ p : ℝ × ℝ, Real.log |p.1 - p.2| ∂rho.prod rho =
      ∑ j : Fin 16, ((rhoPartial (j + 1) : ℝ) ^ 2 - (rhoPartial j : ℝ) ^ 2) *
        Real.log (((rhoB j : ℝ) - rhoA j) / 4) := by
  rw [rho_prod_rho, integral_finsetSum_measure fun p _ ↦
    (integrable_log_abs_sub_arcsineMeasure_rho p.1 p.2).smul_measure
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_log_abs_sub_arcsineMeasure_rho, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by exact_mod_cast rhoC_nonneg _ : (0 : ℝ) ≤ rhoC _), smul_eq_mul,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [rhoPartial_succ_eq_sum_filter, rhoPartial_eq_sum_filter, Rat.cast_sum]
  exact sum_sum_mul_mul_max (fun i ↦ (rhoC i : ℝ)) fun m ↦
    Real.log (((rhoB m : ℝ) - rhoA m) / 4)

/-- `(t, u) ↦ log |t - u|` is integrable against `ρ ⊗ ρ`, with `ρ` viewed as a measure on
`ℂ`: the logarithmic energy of `ρ` is given by an absolutely convergent integral. -/
@[zeta5irr "lem_rho_energy_formula"]
theorem integrable_log_norm_sub_rho :
    Integrable (fun p : ℂ × ℂ ↦ Real.log ‖p.1 - p.2‖)
      ((rho.map ((↑) : ℝ → ℂ)).prod (rho.map ((↑) : ℝ → ℂ))) := by
  rw [Measure.map_prod_map _ _ Complex.measurable_ofReal Complex.measurable_ofReal,
    integrable_map_measure (by fun_prop : Measurable fun p : ℂ × ℂ ↦
      Real.log ‖p.1 - p.2‖).aestronglyMeasurable (by fun_prop)]
  refine integrable_log_abs_sub_rho_prod.congr (Filter.Eventually.of_forall fun p ↦ ?_)
  simp [← Complex.ofReal_sub, Complex.norm_real]

/-- `ρ` gives no mass to points. -/
theorem rho_singleton (x : ℝ) : rho {x} = 0 := by
  rw [rho_apply]
  exact Finset.sum_eq_zero fun j _ ↦ mul_eq_zero_of_right _
    (withDensity_absolutelyContinuous _ _ (Real.volume_singleton))

/-- If `ν` gives no mass to points, the diagonal `{p | p.1 = p.2}` is `μ ⊗ ν`-null. -/
theorem prod_setOf_fst_eq_snd_eq_zero {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (μ ν : Measure α) [SFinite ν] (hν : ∀ x, ν {x} = 0) :
    (μ.prod ν) {p | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  refine (lintegral_congr fun x ↦ ?_).trans lintegral_zero
  have : Prod.mk x ⁻¹' {p : α × α | p.1 = p.2} = {x} := by
    ext; simp [eq_comm]
  rw [this, hν]

/-- The diagonal `{t = u}` is null for `ρ ⊗ ρ`, with `ρ` viewed as a measure on `ℂ`: the
integrand `log |t - u|` of the energy is finite `ρ ⊗ ρ`-almost everywhere. -/
@[zeta5irr "lem_rho_energy_formula"]
theorem rho_map_prod_diagonal :
    ((rho.map ((↑) : ℝ → ℂ)).prod (rho.map ((↑) : ℝ → ℂ))) {p | p.1 = p.2} = 0 := by
  refine prod_setOf_fst_eq_snd_eq_zero _ _ fun x ↦ ?_
  rw [Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton x)]
  refine measure_mono_null (fun y hy ↦ ?_) (rho_singleton x.re)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
  rw [← hy, Complex.ofReal_re]

/-- **The energy of `ρ`.** `I(ρ) = ∑_{j=1}^{16} (Sⱼ² - S_{j-1}²) log ((bⱼ - aⱼ)/4)`. -/
@[zeta5irr "lem_rho_energy_formula"]
theorem logEnergy_rho :
    logEnergy (rho.map ((↑) : ℝ → ℂ)) =
      ∑ j : Fin 16, ((rhoPartial (j + 1) : ℝ) ^ 2 - (rhoPartial j : ℝ) ^ 2) *
        Real.log (((rhoB j : ℝ) - rhoA j) / 4) := by
  rw [logEnergy, Measure.map_prod_map _ _ Complex.measurable_ofReal Complex.measurable_ofReal,
    integral_map (by fun_prop) (by fun_prop : Measurable fun p : ℂ × ℂ ↦
      Real.log ‖p.1 - p.2‖).aestronglyMeasurable, ← integral_log_abs_sub_rho_prod]
  congr 1 with p
  simp [← Complex.ofReal_sub, Complex.norm_real]

end Zeta5Irr
