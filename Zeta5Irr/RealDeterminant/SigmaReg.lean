/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigCircle
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# The regularised configuration measure

For a tuple `t = (t₁, …, t_h)` of points and `ε > 0`, the measure
`σ_{t,ε} = K⁻¹ ∑_{i = 1}^{h} ϖ_{t_i,ε}` spreads a mass `1 / K` uniformly over each circle
`|z - t_i| = ε`, regularising the atomic configuration measure `K⁻¹ ∑ δ_{t_i}`. It is
a finite positive Borel measure of total mass `h / K`.

## Main definitions

* `Zeta5Irr.sigmaReg K t ε`: the measure `σ_{t,ε} = K⁻¹ ∑_i ϖ_{t_i,ε}`.

## Main results

* `Zeta5Irr.sigmaReg_apply`, `Zeta5Irr.lintegral_sigmaReg`, `Zeta5Irr.integral_sigmaReg`:
  the mass of a set, and the (lower Lebesgue or Bochner) integral of a function, against
  `σ_{t,ε}` are `K⁻¹` times the sum of those against the circle measures.
* `Zeta5Irr.sigmaReg_univ`: `σ_{t,ε}` has total mass `h / K`.
* `Zeta5Irr.sigmaReg.instIsFiniteMeasure`: `σ_{t,ε}` is a finite measure.
* `Zeta5Irr.ae_sigmaReg_exists_mem_sphere`: `σ_{t,ε}` is carried by the union of the
  circles `|z - t_i| = |ε|`.

## Implementation notes

* The source fixes `K = 40 n`, the pole bound `Zeta5Irr.poleBound n`; here `K` is an
  arbitrary natural number, the source's measure being `sigmaReg (poleBound n) t ε`.
  For `K = 0` the normalising factor `K⁻¹` is `∞` in `ℝ≥0∞`, which no statement uses.
* The source takes `t ∈ [0, ∞)^h`; the definition makes sense, and its API holds, for any
  `t : Fin h → ℂ` and any real `ε`, so neither the sign conditions nor `ε > 0` is imposed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2: a bound for every configuration.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal

namespace Zeta5Irr

variable {h : ℕ}

/-- The regularised configuration measure `σ_{t,ε} = K⁻¹ ∑_{i = 1}^{h} ϖ_{t_i,ε}`: mass
`1 / K` spread uniformly on each circle `|z - t_i| = ε`. -/
@[zeta5irr "def_sigma_reg"]
noncomputable def sigmaReg (K : ℕ) (t : Fin h → ℂ) (ε : ℝ) : Measure ℂ :=
  (K : ℝ≥0∞)⁻¹ • ∑ i, circleUnif (t i) ε

variable (K : ℕ) (t : Fin h → ℂ) (ε : ℝ)

/-- The `σ_{t,ε}`-mass of a set `s` is `K⁻¹ ∑_i ϖ_{t_i,ε}(s)`. -/
theorem sigmaReg_apply (s : Set ℂ) :
    sigmaReg K t ε s = (K : ℝ≥0∞)⁻¹ * ∑ i, circleUnif (t i) ε s := by
  rw [sigmaReg, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]

/-- `σ_{t,ε}` has total mass `h / K`. -/
theorem sigmaReg_univ : sigmaReg K t ε Set.univ = (K : ℝ≥0∞)⁻¹ * h := by
  simp [sigmaReg_apply]

/-- For `K ≠ 0`, `σ_{t,ε}` is a finite measure. -/
instance sigmaReg.instIsFiniteMeasure [NeZero K] : IsFiniteMeasure (sigmaReg K t ε) :=
  ⟨by
    rw [sigmaReg_univ]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simpa using NeZero.pos K))
      (ENNReal.natCast_lt_top h)⟩

/-- The lower Lebesgue integral of `f` against `σ_{t,ε}` is
`K⁻¹ ∑_i ∫⁻ f ∂ϖ_{t_i,ε}`. -/
theorem lintegral_sigmaReg (f : ℂ → ℝ≥0∞) :
    ∫⁻ z, f z ∂sigmaReg K t ε = (K : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ z, f z ∂circleUnif (t i) ε := by
  rw [sigmaReg, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]

/-- If `f` is integrable against each circle measure `ϖ_{t_i,ε}`, its integral against
`σ_{t,ε}` is `K⁻¹ ∑_i ∫ f ∂ϖ_{t_i,ε}`. -/
theorem integral_sigmaReg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} (hf : ∀ i, Integrable f (circleUnif (t i) ε)) :
    ∫ z, f z ∂sigmaReg K t ε = (K : ℝ)⁻¹ • ∑ i, ∫ z, f z ∂circleUnif (t i) ε := by
  rw [sigmaReg, integral_smul_measure, integral_finsetSum_measure fun i _ ↦ hf i]
  simp

/-- For `K ≠ 0`, a function is integrable against `σ_{t,ε}` if and only if it is
integrable against each circle measure `ϖ_{t_i,ε}`. -/
theorem integrable_sigmaReg_iff {E : Type*} [NormedAddCommGroup E] [NeZero K] {f : ℂ → E} :
    Integrable f (sigmaReg K t ε) ↔ ∀ i, Integrable f (circleUnif (t i) ε) := by
  rw [sigmaReg, integrable_smul_measure (by simp) (by simp [NeZero.ne K]),
    integrable_finsetSum_measure]
  simp

/-- `σ_{t,ε}` gives no mass to the complement of the union of the circles
`|z - t_i| = |ε|`. -/
theorem sigmaReg_compl_iUnion_sphere : sigmaReg K t ε (⋃ i, sphere (t i) |ε|)ᶜ = 0 := by
  rw [sigmaReg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
  exact measure_mono_null (Set.compl_subset_compl.2 (Set.subset_iUnion _ i))
    (circleUnif_sphere_compl _ _)

/-- `σ_{t,ε}`-almost every point lies on one of the circles `|z - t_i| = |ε|`. -/
theorem ae_sigmaReg_exists_mem_sphere : ∀ᵐ z ∂sigmaReg K t ε, ∃ i, z ∈ sphere (t i) |ε| := by
  have := sigmaReg_compl_iUnion_sphere K t ε
  rw [← mem_ae_iff] at this
  filter_upwards [this] with z hz
  simpa using hz

end Zeta5Irr
