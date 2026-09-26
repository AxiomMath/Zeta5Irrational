/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The zero-mass logarithmic energy integral

For `0 < a` and `0 < b`, the Frullani-type integral
`∫₀^∞ (e^{-as} - e^{-bs}) / s ds` converges absolutely and equals `log (b / a)`.
The proof writes `(e^{-as} - e^{-bs}) / s = ∫_a^b e^{-sv} dv` and exchanges the order of
integration (Fubini–Tonelli), using `∫₀^∞ e^{-sv} ds = 1 / v` and `∫_a^b dv / v = log (b / a)`.

Specialising to `a = 1`, `b = r²` gives, for every `r > 0`,
`(1/2) ∫₀^∞ (e^{-s} - e^{-s r²}) / s ds = log r`.

## Main results

* `Zeta5Irr.integrableOn_exp_neg_mul_sub_exp_neg_mul_div`: the integrand
  `(e^{-as} - e^{-bs}) / s` is integrable on `(0, ∞)`.
* `Zeta5Irr.integral_exp_neg_mul_sub_exp_neg_mul_div`:
  `∫₀^∞ (e^{-as} - e^{-bs}) / s ds = log (b / a)`.
* `Zeta5Irr.half_integral_exp_neg_sub_exp_neg_mul_sq_div`:
  `(1/2) ∫₀^∞ (e^{-s} - e^{-s r²}) / s ds = log r` for `r > 0`.

## Implementation notes

* The integral over `(0, ∞)` is a Bochner integral over `Set.Ioi 0`; the integrability lemma
  records that it converges absolutely, so the identity is not an artefact of the convention
  that non-integrable functions have integral `0`.
* The blueprint's case split `r > 1`, `r < 1`, `r = 1` becomes the case split `a ≤ b` versus
  `b ≤ a` in the general two-parameter statement.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1: zero-mass logarithmic energy.
-/

@[expose] public section

open MeasureTheory Set Real

namespace Zeta5Irr

/-- For `0 < s`, `∫_{(a, b]} e^{-vs} dv = (e^{-as} - e^{-bs}) / s`. -/
theorem integral_Ioc_exp_neg_mul {a b s : ℝ} (hab : a ≤ b) (hs : 0 < s) :
    ∫ v in Ioc a b, exp (-v * s) = (exp (-a * s) - exp (-b * s)) / s := by
  rw [← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ v ∈ uIcc a b, HasDerivAt (fun v => -exp (-v * s) / s) (exp (-v * s)) v := by
    intro v _
    have h1 : HasDerivAt (fun v => -v * s) (-s) v := by
      simpa using (hasDerivAt_id v).neg.mul_const s
    convert h1.exp.neg.div_const s using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_exp.comp (continuous_neg.mul continuous_const)).intervalIntegrable _ _)]
  ring

/-- Integrability on the product and the value of the Frullani integral, for `a ≤ b`. -/
private theorem integrableOn_and_integral_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun s => (exp (-a * s) - exp (-b * s)) / s) (Ioi 0) ∧
      ∫ s in Ioi 0, (exp (-a * s) - exp (-b * s)) / s = log (b / a) := by
  set μ : Measure ℝ := volume.restrict (Ioi 0)
  set ν : Measure ℝ := volume.restrict (Ioc a b)
  set F : ℝ × ℝ → ℝ := fun p => exp (-p.2 * p.1)
  have hFc : Continuous F := by fun_prop
  have hinner : ∀ v ∈ Ioc a b, ∫ s in Ioi 0, exp (-v * s) = v⁻¹ := by
    intro v hv
    have hv0 : 0 < v := ha.trans hv.1
    rw [integral_exp_mul_Ioi (by linarith) 0]
    simp [neg_div]
  have hinv : IntegrableOn (fun v : ℝ => v⁻¹) (Ioc a b) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun v hv => (ha.trans_le hv.1).ne'
  have hint : Integrable F (μ.prod ν) := by
    rw [integrable_prod_iff' hFc.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact exp_neg_integrableOn_Ioi 0 (ha.trans hv.1)
    · refine hinv.congr_fun (fun v hv => ?_) measurableSet_Ioc
      simp only [F, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact (hinner v hv).symm
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ∫ v, F (s, v) ∂ν = (exp (-a * s) - exp (-b * s)) / s :=
    fun s hs => integral_Ioc_exp_neg_mul hab hs
  refine ⟨IntegrableOn.congr_fun (hint.integral_prod_left :
    IntegrableOn (fun s => ∫ v, F (s, v) ∂ν) (Ioi (0 : ℝ)) volume) hpt
    measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hpt]
  change ∫ s, ∫ v, exp (-v * s) ∂ν ∂μ = _
  rw [integral_integral_swap (f := fun s v => exp (-v * s)) hint,
    setIntegral_congr_fun measurableSet_Ioc hinner, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha (ha.trans_le hab)]

/-- For `0 < a` and `0 < b`, the integrand `(e^{-as} - e^{-bs}) / s` is integrable on
`(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_sub_exp_neg_mul_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s => (exp (-a * s) - exp (-b * s)) / s) (Ioi 0) := by
  rcases le_total a b with hab | hba
  · exact (integrableOn_and_integral_of_le ha hab).1
  · refine ((integrableOn_and_integral_of_le hb hba).1.neg).congr_fun (fun s _ => ?_)
      measurableSet_Ioi
    simp only [Pi.neg_apply]
    ring

/-- **Frullani's integral for the exponential.** For `0 < a` and `0 < b`,
`∫₀^∞ (e^{-as} - e^{-bs}) / s ds = log (b / a)`. -/
theorem integral_exp_neg_mul_sub_exp_neg_mul_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ s in Ioi 0, (exp (-a * s) - exp (-b * s)) / s = log (b / a) := by
  rcases le_total a b with hab | hba
  · exact (integrableOn_and_integral_of_le ha hab).2
  · have h := (integrableOn_and_integral_of_le hb hba).2
    have heq : (fun s => (exp (-a * s) - exp (-b * s)) / s) =
        fun s => -((exp (-b * s) - exp (-a * s)) / s) := by
      ext s; ring
    rw [heq, integral_neg, h, log_div hb.ne' ha.ne', log_div ha.ne' hb.ne']
    ring

/-- **Zero-mass logarithmic energy.** For every `r > 0`,
`(1/2) ∫₀^∞ (e^{-s} - e^{-s r²}) / s ds = log r`. -/
@[zeta5irr "lem_energy_log_integral"]
theorem half_integral_exp_neg_sub_exp_neg_mul_sq_div {r : ℝ} (hr : 0 < r) :
    (1 / 2) * ∫ s in Ioi 0, (exp (-s) - exp (-s * r ^ 2)) / s = log r := by
  have h := integral_exp_neg_mul_sub_exp_neg_mul_div one_pos (pow_pos hr 2)
  have heq : (fun s : ℝ => (exp (-s) - exp (-s * r ^ 2)) / s) =
      fun s => (exp (-1 * s) - exp (-(r ^ 2) * s)) / s := by
    ext s; ring_nf
  rw [heq, h, div_one, log_pow]
  push_cast
  ring

end Zeta5Irr
