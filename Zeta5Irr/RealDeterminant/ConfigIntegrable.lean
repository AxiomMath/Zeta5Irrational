/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.SigmaReg
public import Zeta5Irr.RealDeterminant.ConfigMutual
public import Zeta5Irr.Measure.RhoEnergyFormula

/-!
# Logarithmic integrability of the comparison pair

Let `ε > 0`, let `t = (t₁, …, t_h)` be a tuple of points and let `η = σ_{t,ε} + ρ`, the sum of
the regularised configuration measure and the rational arcsine measure `ρ` (viewed as a
measure on `ℂ`). Then the logarithmic kernel is absolutely integrable against `η ⊗ η`:
`∬ |log |z - w|| dη(z) dη(w) < ∞`.

The proof expands `η ⊗ η` into the products of the circle measures `ϖ_{t_i,ε}` and `ρ`. For a
circle measure `ϖ_{c,ε}` against any finite measure `μ` carried by a disc, the inner integral
`∫ |log |z - w|| dϖ_{c,ε}(z)` is bounded uniformly in `w` in the disc, which gives
integrability against `ϖ_{c,ε} ⊗ μ`; the products `ρ ⊗ ϖ_{c,ε}` follow by the coordinate
swap, and `ρ ⊗ ρ` is the absolute convergence of the energy of `ρ`.

## Main results

* `Zeta5Irr.integrable_log_norm_sub_sigmaReg_prod`: `(z, w) ↦ log |z - w|` is integrable
  against `σ_{t,ε} ⊗ μ` for every finite measure `μ` carried by a disc.
* `Zeta5Irr.integrable_log_norm_sub_sigmaReg_add_rho_prod`: `(z, w) ↦ log |z - w|` is
  integrable against `η ⊗ η`, where `η = σ_{t,ε} + ρ`.
* `Zeta5Irr.sigmaReg_add_rho_prod_diagonal`: the diagonal is `η ⊗ η`-null.

## Implementation notes

* In Lean `Real.log 0 = 0`, whereas the source's integrand `|log |z - w||` is `+∞` on the
  diagonal. The source's statement is therefore the conjunction of the integrability of
  `(z, w) ↦ log ‖z - w‖` against `η ⊗ η` and the vanishing of the `η ⊗ η`-measure of the
  diagonal; both are proved.
* The source takes `t ∈ [0, ∞)^h` and normalises `σ_{t,ε}` by `K = 40 n`; here `t` is any
  tuple of complex numbers and `K` any nonzero natural number.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

open MeasureTheory Real Set Metric
open scoped ENNReal

namespace Zeta5Irr

/-- `(z, w) ↦ log |z - w|` is integrable against `σ_{t,ε} ⊗ μ` for every finite measure `μ`
carried by a disc. -/
theorem integrable_log_norm_sub_sigmaReg_prod {h : ℕ} (K : ℕ) [NeZero K] (t : Fin h → ℂ)
    {ε : ℝ} (hε : 0 < ε) {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (hμ : ∀ᵐ w ∂μ, ‖w‖ ≤ R) :
    Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖) ((sigmaReg K t ε).prod μ) := by
  rw [sigmaReg, Measure.prod_smul_left, ← Measure.sum_fintype, Measure.prod_sum_left,
    Measure.sum_fintype]
  refine Integrable.smul_measure ?_ (by simp [NeZero.ne K])
  exact integrable_finsetSum_measure.2 fun i _ =>
    integrable_log_norm_sub_circleUnif_prod hμ (t i) hε

/-- `σ_{t,ε}` is carried by a disc. -/
theorem ae_norm_le_sigmaReg {h : ℕ} (K : ℕ) (t : Fin h → ℂ) (ε : ℝ) :
    ∀ᵐ z ∂sigmaReg K t ε, ‖z‖ ≤ ∑ i, ‖t i‖ + |ε| := by
  filter_upwards [ae_sigmaReg_exists_mem_sphere K t ε] with z ⟨i, hi⟩
  rw [mem_sphere, dist_eq_norm] at hi
  calc ‖z‖ = ‖(z - t i) + t i‖ := by ring_nf
    _ ≤ ‖z - t i‖ + ‖t i‖ := norm_add_le _ _
    _ ≤ ∑ i, ‖t i‖ + |ε| := by
      rw [hi, add_comm]
      gcongr
      exact Finset.single_le_sum (f := fun i => ‖t i‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)

/-- `ρ`, viewed as a measure on `ℂ`, is carried by the disc of radius `2`. -/
theorem ae_norm_le_two_rho_map : ∀ᵐ z ∂rho.map ((↑) : ℝ → ℂ), ‖z‖ ≤ 2 := by
  rw [ae_map_iff Complex.measurable_ofReal.aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet]
  filter_upwards [ae_mem_Icc_rho] with x hx
  have h0 : (0 : ℝ) < rhoA 15 := by exact_mod_cast rhoA_fifteen_pos
  have h2 : (rhoB 15 : ℝ) < 2 := by exact_mod_cast rhoB_fifteen_lt_two
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
  linarith [hx.2]

/-- **Logarithmic integrability of the comparison pair.** For `ε > 0` and
`η = σ_{t,ε} + ρ`, the function `(z, w) ↦ log |z - w|` is integrable against `η ⊗ η`, that
is `∬ |log |z - w|| dη(z) dη(w) < ∞`. -/
@[zeta5irr "lem_config_integrable"]
theorem integrable_log_norm_sub_sigmaReg_add_rho_prod {h : ℕ} (K : ℕ) [NeZero K]
    (t : Fin h → ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => log ‖p.1 - p.2‖)
      ((sigmaReg K t ε + rho.map ((↑) : ℝ → ℂ)).prod
        (sigmaReg K t ε + rho.map ((↑) : ℝ → ℂ))) := by
  set σ := sigmaReg K t ε
  set ρ' := rho.map ((↑) : ℝ → ℂ)
  have hη : ∀ᵐ z ∂(σ + ρ'), ‖z‖ ≤ max (∑ i, ‖t i‖ + |ε|) 2 := by
    rw [ae_add_measure_iff]
    exact ⟨(ae_norm_le_sigmaReg K t ε).mono fun _ h => h.trans (le_max_left _ _),
      ae_norm_le_two_rho_map.mono fun _ h => h.trans (le_max_right _ _)⟩
  rw [Measure.add_prod]
  refine (integrable_log_norm_sub_sigmaReg_prod K t hε hη).add_measure ?_
  rw [Measure.prod_add]
  refine Integrable.add_measure ?_ integrable_log_norm_sub_rho
  rw [← integrable_swap_iff]
  refine (integrable_log_norm_sub_sigmaReg_prod K t hε ae_norm_le_two_rho_map).congr
    (Filter.Eventually.of_forall fun p => ?_)
  simp [norm_sub_rev]

/-- The diagonal `{z = w}` is `η ⊗ η`-null, where `η = σ_{t,ε} + ρ` and `ε ≠ 0`: the
integrand `|log |z - w||` is finite `η ⊗ η`-almost everywhere. -/
@[zeta5irr "lem_config_integrable"]
theorem sigmaReg_add_rho_prod_diagonal {h : ℕ} (K : ℕ) [NeZero K] (t : Fin h → ℂ) {ε : ℝ}
    (hε : ε ≠ 0) :
    ((sigmaReg K t ε + rho.map ((↑) : ℝ → ℂ)).prod
      (sigmaReg K t ε + rho.map ((↑) : ℝ → ℂ))) {p | p.1 = p.2} = 0 := by
  refine prod_setOf_fst_eq_snd_eq_zero _ _ fun z => ?_
  rw [Measure.add_apply, sigmaReg_apply,
    Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton z)]
  simp only [circleUnif_singleton _ _ hε, Finset.sum_const_zero, mul_zero, zero_add]
  refine measure_mono_null (fun x hx => ?_) (rho_singleton z.re)
  simp only [mem_preimage, mem_singleton_iff] at hx ⊢
  rw [← hx, Complex.ofReal_re]

end Zeta5Irr
