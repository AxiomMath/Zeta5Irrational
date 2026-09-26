/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotM0Notation
public import Zeta5Irr.Measure.PotBoundDominates
public import Zeta5Irr.Measure.PotPartition
public import Zeta5Irr.Measure.PotTableBound
public import Zeta5Irr.Measure.VDecay
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The potential inequality on the half-line

For every `t ≥ 0`, `2 U^ρ(t) - V(t) ≤ M₀ = -1329/200`, where `U^ρ` is the logarithmic
potential of the comparison measure `ρ` and `V` is the external field.

On `[0, 2]` the point `t` lies in one of the dyadic intervals `J_{j,d,k} = [l, r]` of the
refinement table, whose left endpoint is nonnegative; there `2 U^ρ(t) - V(t) ≤ 𝓑(l, r)`, and
the table bound gives `𝓑(l, r) < -6645002/10⁶ < M₀`. On `[2, ∞)` the decay estimate gives
`2 U^ρ(t) - V(t) ≤ g(t) = (13/10) log t + 6 α³ / t - 2π √t`, and `g(t) ≤ g(2) < M₀`.

## Main results

* `Zeta5Irr.two_mul_logPotential_rho_sub_externalField_le_potentialBound`: for `t ≥ 0`,
  `2 U^ρ(t) - V(t) ≤ M₀`.

## Implementation notes

The source shows `g(t) ≤ g(2)` for `t ≥ 2` by the sign of `g'`. We argue without derivatives:
`6 α³ / t ≤ 6 α³ / 2`, and, writing `s = √t / √2 ≥ 1`, the inequality `log s ≤ s - 1` gives
`(13/10) (log t - log 2) = (13/5) log s ≤ (13/(5√2)) (√t - √2) ≤ 2π (√t - √2)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.7 (The potential inequality on the half-line).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The decay bound `g(t) = (13/10) log t + 6 α³ / t - 2π √t` lies below `M₀` for `t ≥ 2`. -/
theorem decayBound_le_potentialBound {t : ℝ} (ht : 2 ≤ t) :
    13 / 10 * log t + 6 * (innerRatio : ℝ) ^ 3 / t - 2 * π * √t ≤ (potentialBound : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hM : (potentialBound : ℝ) = -1329 / 200 := by norm_num [potentialBound]
  rw [hα, hM]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have h75 : (7 / 5 : ℝ) < √2 := by
    rw [lt_sqrt (by norm_num)]; norm_num
  have hst : √2 ≤ √t := sqrt_le_sqrt ht
  -- `log t - log 2 = 2 log (√t / √2) ≤ 2 (√t / √2 - 1)`
  have hlog : log t - log 2 ≤ 2 * (√t / √2 - 1) := by
    have hs : 0 < √t / √2 := by positivity
    have := log_le_sub_one_of_pos hs
    rw [log_div (sqrt_pos.2 ht0).ne' h2.ne', log_sqrt ht0.le, log_sqrt (by norm_num)] at this
    linarith
  have hdiv : 2 * (√t / √2 - 1) = √2 * (√t - √2) := by
    field_simp
    nlinarith [hs2]
  have hgap : 0 ≤ √t - √2 := sub_nonneg.2 hst
  have hπ := pi_gt_three
  have hl2 := log_two_lt_d9
  have hinv : 6 * (3 / 40 : ℝ) ^ 3 / t ≤ 6 * (3 / 40) ^ 3 / 2 := by
    gcongr
  have hkey : 13 / 10 * (√2 * (√t - √2)) ≤ 2 * π * (√t - √2) := by
    have : 13 / 10 * √2 ≤ 2 * π := by nlinarith [hs2]
    nlinarith
  nlinarith

set_option maxRecDepth 4000 in
/-- **The potential inequality on the half-line**: for `t ≥ 0`, `2 U^ρ(t) - V(t) ≤ M₀`, where
`M₀ = -1329/200`. -/
@[zeta5irr "lem_rho_potential"]
theorem two_mul_logPotential_rho_sub_externalField_le_potentialBound {t : ℝ} (ht : 0 ≤ t) :
    2 * logPotential (rho.map ((↑) : ℝ → ℂ)) t - externalField t ≤ (potentialBound : ℝ) := by
  rcases le_total t 2 with ht2 | ht2
  · obtain ⟨j, d, k, hk, hmem⟩ := exists_mem_potTable_mem_potInterval ht ht2
    obtain ⟨hl, hr⟩ := mem_potInterval.1 hmem
    have hA : (0 : ℝ) ≤ potGrid j.castSucc := by
      have := strictMono_potGrid.monotone (Fin.zero_le j.castSucc)
      rw [potGrid_zero] at this
      exact_mod_cast this
    have hΔ : (0 : ℝ) ≤ potGrid j.succ - potGrid j.castSucc :=
      sub_nonneg.2 (Rat.cast_le.2 (strictMono_potGrid Fin.castSucc_lt_succ).le)
    have hl0 : 0 ≤ potIntervalLeft j d k := by
      rw [potIntervalLeft]; positivity
    have hB := two_mul_logPotential_rho_sub_externalField_le_potBound hl0 hl hr
    have hT := potBound_potInterval_lt hk
    have hM : (potentialBound : ℝ) = -1329 / 200 := by norm_num [potentialBound]
    rw [hM]
    have : -6645002 / (10 : ℝ) ^ 6 < -1329 / 200 := by norm_num
    linarith
  · exact (two_mul_logPotential_rho_sub_externalField_le ht2).trans
      (decayBound_le_potentialBound ht2)

end Zeta5Irr
