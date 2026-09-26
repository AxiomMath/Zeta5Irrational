/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExOuterIntegrand
public import Zeta5Irr.PrimeSum.NormPwc

/-!
# Piecewise continuity of the outer integrand `Θ`

For every real `u` with `1/3 < u < 2 λ`, the outer integrand
`Θ(y) = R₀(y) - d_rk(y) - 2 λ ⌊1/y⌋ + ∑_{j=1}^{5} (2 λ - j y)⁺` is piecewise continuous on
`[u, 2 λ]`. Indeed, on each of `(1/3, 1/2]`, `(1/2, 1]` and `(1, ∞)` the function `R₀` is
given by a fixed expression built from `min` and the positive part, `d_rk` agrees with a
fixed continuous expression, and `⌊1/y⌋` is constant (equal to `2`, `1` and `0`
respectively). So `Θ` agrees with a function continuous on all of `ℝ` on each of the three
ranges; cutting `[u, 2 λ]` at those of `1/2` and `1` that lie inside gives the partition,
and the three continuous functions bound `Θ` on the compact interval.

## Main results

* `Zeta5Irr.outerIntegrand_eq_of_le_half`, `Zeta5Irr.outerIntegrand_eq_of_half_lt_of_le_one`:
  the closed form of `Θ` on `(1/3, 1/2]` and on `(1/2, 1]`.
* `Zeta5Irr.piecewiseContinuousOn_outerIntegrand_of_le`: `Θ` is piecewise continuous on
  `[u, 2 λ]` for `1/3 ≤ u < 2 λ`.
* `Zeta5Irr.piecewiseContinuousOn_outerIntegrand`: the case `1/3 < u < 2 λ` of the source.

## Implementation notes

* On `(1/3, 1/2]` the rank defect is written without its indicator: the expression
  `(1 + 4 α - 3 y - (1 + α - 3 y)⁺)⁺` vanishes at `y = 1/2`, so it agrees with `d_rk` on
  the half-closed range, and `Θ` agrees on each range with one continuous function
  including its right endpoint.
* In `[u, 2 λ]` with `u > 1/3` the jumps of `⌊1/y⌋` are at `1/2` and `1` only, which are
  already cut points of `R₀`, so no further refinement of the partition is needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8 (The growth of the normalizing factor).
-/

@[expose] public section

namespace Zeta5Irr

open Set

/-- On `(1/3, 1/2]`, `⌊1/y⌋ = 2`, `R₀` is its first branch and `d_rk` is the double positive
part without its indicator. -/
theorem outerIntegrand_eq_of_le_half {y : ℝ} (hy₁ : 1 / 3 < y) (hy₂ : y ≤ 1 / 2) :
    outerIntegrand y =
      8 - 9 * y - 8 * (innerRatio : ℝ) - 5 * min (innerRatio : ℝ) (1 - 2 * y) -
        5 * (1 + (innerRatio : ℝ) - 3 * y)⁺ -
        (1 + 4 * (innerRatio : ℝ) - 3 * y - (1 + (innerRatio : ℝ) - 3 * y)⁺)⁺ -
        2 * (orderRatio : ℝ) * 2 +
        ∑ j ∈ Finset.Icc 1 5, (2 * (orderRatio : ℝ) - (j : ℕ) * y)⁺ := by
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hy0 : 0 < y := by linarith
  have hfl : ⌊y⁻¹⌋ = 2 := by
    rw [Int.floor_eq_iff, le_inv_comm₀ (by norm_num) hy0, inv_lt_comm₀ hy0 (by norm_num)]
    constructor <;> push_cast <;> linarith
  have hd : rankDefect y =
      (1 + 4 * (innerRatio : ℝ) - 3 * y - (1 + (innerRatio : ℝ) - 3 * y)⁺)⁺ := by
    rcases hy₂.lt_or_eq with h | h
    · exact rankDefect_of_mem hy₁ h
    · subst h
      rw [rankDefect_of_one_half_le le_rfl, hα, eq_comm, posPart_eq_zero,
        posPart_eq_zero.2 (by norm_num)]
      norm_num
  rw [outerIntegrand, outerLimitingFunction_of_le_half hy₂, hd, hfl]
  push_cast
  ring

/-- On `(1/2, 1]`, `⌊1/y⌋ = 1`, `R₀` is its second branch and `d_rk = 0`. -/
theorem outerIntegrand_eq_of_half_lt_of_le_one {y : ℝ} (hy₁ : 1 / 2 < y) (hy₂ : y ≤ 1) :
    outerIntegrand y =
      7 * (1 - y) - 6 * min (innerRatio : ℝ) (1 - y) -
        6 * (1 + (innerRatio : ℝ) - 2 * y)⁺ + (1 + 4 * (innerRatio : ℝ) - 2 * y)⁺ -
        2 * (orderRatio : ℝ) +
        ∑ j ∈ Finset.Icc 1 5, (2 * (orderRatio : ℝ) - (j : ℕ) * y)⁺ := by
  have hy0 : 0 < y := by linarith
  have hfl : ⌊y⁻¹⌋ = 1 := by
    rw [Int.floor_eq_iff, le_inv_comm₀ (by norm_num) hy0, inv_lt_comm₀ hy0 (by norm_num)]
    constructor <;> push_cast <;> linarith
  rw [outerIntegrand, outerLimitingFunction_of_half_lt_of_le_one hy₁ hy₂,
    rankDefect_of_one_half_le hy₁.le, hfl]
  push_cast
  ring

/-- On `(1/3, 1/2]` the outer integrand agrees with a continuous function. -/
theorem exists_continuous_eqOn_outerIntegrand_Ioc_third_half :
    ∃ g : ℝ → ℝ, Continuous g ∧ EqOn outerIntegrand g (Ioc (1 / 3) (1 / 2)) := by
  refine ⟨_, ?_, fun y hy => outerIntegrand_eq_of_le_half hy.1 hy.2⟩
  simp only [posPart_def]
  fun_prop

/-- On `(1/2, 1]` the outer integrand agrees with a continuous function. -/
theorem exists_continuous_eqOn_outerIntegrand_Ioc_half_one :
    ∃ g : ℝ → ℝ, Continuous g ∧ EqOn outerIntegrand g (Ioc (1 / 2) 1) := by
  refine ⟨_, ?_, fun y hy => outerIntegrand_eq_of_half_lt_of_le_one hy.1 hy.2⟩
  simp only [posPart_def]
  fun_prop

/-- On `(1, ∞)` the outer integrand agrees with a continuous function. -/
theorem exists_continuous_eqOn_outerIntegrand_Ioi_one :
    ∃ g : ℝ → ℝ, Continuous g ∧ EqOn outerIntegrand g (Ioi 1) := by
  refine ⟨_, ?_, fun y hy => outerIntegrand_of_one_lt hy⟩
  simp only [posPart_def]
  fun_prop

/-- For every `u` with `1/3 ≤ u < 2 λ`, the outer integrand `Θ` is piecewise continuous on
`[u, 2 λ]`: the closed form valid on `(1/3, 1/2]` is continuous on `[1/3, 1/2]`. -/
theorem piecewiseContinuousOn_outerIntegrand_of_le {u : ℝ} (hu₁ : 1 / 3 ≤ u)
    (hu₂ : u < 2 * (orderRatio : ℝ)) :
    PiecewiseContinuousOn outerIntegrand u (2 * (orderRatio : ℝ)) := by
  have hlam : (orderRatio : ℝ) = 37 / 40 := by norm_num [orderRatio]
  obtain ⟨g₁, hc₁, e₁⟩ := exists_continuous_eqOn_outerIntegrand_Ioc_third_half
  obtain ⟨g₂, hc₂, e₂⟩ := exists_continuous_eqOn_outerIntegrand_Ioc_half_one
  obtain ⟨g₃, hc₃, e₃⟩ := exists_continuous_eqOn_outerIntegrand_Ioi_one
  have hb : ∃ C, ∀ t ∈ Icc u (2 * (orderRatio : ℝ)), |outerIntegrand t| ≤ C := by
    have hK := isCompact_Icc (a := u) (b := 2 * (orderRatio : ℝ))
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hc₁.continuousOn
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hc₂.continuousOn
    obtain ⟨C₃, hC₃⟩ := hK.exists_bound_of_continuousOn hc₃.continuousOn
    refine ⟨max (max C₁ (max C₂ C₃)) |outerIntegrand (1 / 3)|, fun t ht => ?_⟩
    refine le_max_iff.2 ?_
    rcases (hu₁.trans ht.1).eq_or_lt with h₀ | h₀
    · exact .inr (by rw [← h₀])
    refine .inl ?_
    rcases le_or_gt t (1 / 2) with h₁ | h₁
    · rw [e₁ ⟨h₀, h₁⟩]
      exact le_max_of_le_left (hC₁ t ht)
    rcases le_or_gt t 1 with h₂ | h₂
    · rw [e₂ ⟨h₁, h₂⟩]
      exact le_max_of_le_right (le_max_of_le_left (hC₂ t ht))
    · rw [e₃ h₂]
      exact le_max_of_le_right (le_max_of_le_right (hC₃ t ht))
  rcases lt_or_ge u (1 / 2) with hA | hA
  · refine ⟨3, ![u, 1 / 2, 1, 2 * (orderRatio : ℝ)], by norm_num, ?_, rfl, rfl, hb, ?_⟩
    · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i <;> simp [hlam] <;> linarith
    · intro k
      fin_cases k
      · exact ⟨g₁, hc₁.continuousOn, fun y hy =>
          e₁ ⟨by simp at hy; linarith, by simp at hy; linarith⟩⟩
      · exact ⟨g₂, hc₂.continuousOn, fun y hy =>
          e₂ ⟨by simp at hy; linarith, by simp at hy; linarith⟩⟩
      · exact ⟨g₃, hc₃.continuousOn, fun y hy => e₃ (mem_Ioi.2 (by simp at hy; linarith))⟩
  rcases lt_or_ge u 1 with hB | hB
  · refine ⟨2, ![u, 1, 2 * (orderRatio : ℝ)], by norm_num, ?_, rfl, rfl, hb, ?_⟩
    · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i <;> simp [hlam] <;> linarith
    · intro k
      fin_cases k
      · exact ⟨g₂, hc₂.continuousOn, fun y hy =>
          e₂ ⟨by simp at hy; linarith, by simp at hy; linarith⟩⟩
      · exact ⟨g₃, hc₃.continuousOn, fun y hy => e₃ (mem_Ioi.2 (by simp at hy; linarith))⟩
  · refine ⟨1, ![u, 2 * (orderRatio : ℝ)], by norm_num, ?_, rfl, rfl, hb, ?_⟩
    · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i
      simpa using hu₂
    · intro k
      fin_cases k
      exact ⟨g₃, hc₃.continuousOn, fun y hy => e₃ (mem_Ioi.2 (by simp at hy; linarith))⟩

/-- For every `u` with `1/3 < u < 2 λ`, the outer integrand `Θ` is piecewise continuous on
`[u, 2 λ]`. -/
@[zeta5irr "lem_norm_Theta_pwc"]
theorem piecewiseContinuousOn_outerIntegrand {u : ℝ} (hu₁ : 1 / 3 < u)
    (hu₂ : u < 2 * (orderRatio : ℝ)) :
    PiecewiseContinuousOn outerIntegrand u (2 * (orderRatio : ℝ)) :=
  piecewiseContinuousOn_outerIntegrand_of_le hu₁.le hu₂

end Zeta5Irr
