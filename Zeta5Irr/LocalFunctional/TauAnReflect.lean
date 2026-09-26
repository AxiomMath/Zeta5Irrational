/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauAnConv
public import Zeta5Irr.LocalFunctional.TauAnPoly
public import Zeta5Irr.LocalFunctional.TauReflect
public import Zeta5Irr.LocalFunctional.TauTateSubst
public import Mathlib.NumberTheory.Padics.LocalField
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# `τ^an` is odd under the reflection `z ↦ -1 - z`

Let `p ≥ 5` be a prime and `f ∈ 𝒜 = ℚ_p⟨z⟩`. Then `τ^an(f(-1 - z)) = -τ^an(f)`.

For `|u|_p, |c|_p ≤ 1` the coefficient of `z^m` in `f(u + cz)` is `∑_d f_d [z^m](u + cz)^d`, so
`τ^an(f(u + cz))` is the double series `∑_m ∑_d f_d [z^m](u + cz)^d κ_m`. Its terms vanish for
`m > d` and are bounded by `p |f_d|_p`, so they tend to `0` along the cofinite filter of
`ℕ × ℕ`, and the double series may be summed in either order in the complete non-archimedean
field `ℚ_p`. Summing over `m` first gives `τ^an(f(u + cz)) = ∑_d f_d τ^an((u + cz)^d)`.
For `u = c = -1`, the polynomial `(-1 - z)^d` has rational coefficients, and
`τ^an((-1 - z)^d) = τ((-1 - x)^d) = -τ(x^d) = -κ_d` by the reflection antisymmetry of `τ`.

## Main results

* `Zeta5Irr.tauAn_tateSubst`: for `f ∈ ℚ_p⟨z⟩` and `|u|_p, |c|_p ≤ 1`,
  `τ^an(f(u + cz)) = ∑_d f_d τ^an((u + cz)^d)`.
* `Zeta5Irr.tauAn_tateSubst_neg_one_neg_one`: `τ^an(f(-1 - z)) = -τ^an(f)`.

## Implementation notes

The source reduces to polynomials by density and continuity of both sides, and then to
monomials by linearity. Here the reduction is made in one step instead: `τ^an(f(u + cz))` is
expanded as a double series, which is unconditionally summable in `ℚ_p`, and the order of
summation is exchanged. The monomial case is the same as in the source.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- **`τ^an` of an affine substitution.** For a prime `p ≥ 5`, `f ∈ ℚ_p⟨z⟩` and
`|u|_p, |c|_p ≤ 1`, `τ^an(f(u + cz)) = ∑_d f_d τ^an((u + cz)^d)`. -/
theorem tauAn_tateSubst (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p)
    {u c : ℚ_[p]}
    (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    tauAn (tateSubst u c f) = ∑' d, coeff d f * tauAn ((C u + C c * X) ^ d) := by
  set g : ℕ → ℕ → ℚ_[p] := fun m d =>
    coeff d f * coeff m ((C u + C c * X) ^ d) * (kappa m : ℚ_[p]) with hg
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsum : Summable (Function.uncurry g) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hf' := mem_tateAlgebra_iff.mp hf
    rw [Metric.tendsto_atTop] at hf'
    obtain ⟨N, hN⟩ := hf' (ε / p) (div_pos hε hp0)
    rw [Filter.eventually_cofinite]
    refine (Finset.range N ×ˢ Finset.range N).finite_toSet.subset ?_
    rintro ⟨m, d⟩ hmd
    simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hmd
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    have hmd' : m ≤ d := by
      by_contra h
      simp [Function.uncurry, hg, coeff_add_mul_X_pow, h] at hmd
      linarith
    have hdN : d < N := by
      by_contra h
      have h1 := hN d (not_lt.mp h)
      rw [dist_zero_right, norm_norm] at h1
      have h2 : ‖Function.uncurry g (m, d)‖ ≤ ‖coeff d f‖ * p := by
        simp only [Function.uncurry, hg, norm_mul]
        gcongr
        · exact mul_le_of_le_one_right (norm_nonneg _)
            (norm_coeff_add_mul_X_pow_le_one hu hc d m)
        · exact norm_kappa_le hp5 m
      have h3 : ‖coeff d f‖ * p < ε := by
        rwa [lt_div_iff₀ hp0] at h1
      linarith
    exact ⟨by omega, hdN⟩
  have h1 : tauAn (tateSubst u c f) = ∑' m, ∑' d, g m d := by
    rw [tauAn_def]
    refine tsum_congr fun m => ?_
    rw [coeff_tateSubst, ← tsum_mul_right]
  have h2 : ∀ d, ∑' m, g m d = coeff d f * tauAn ((C u + C c * X) ^ d) := by
    intro d
    rw [tauAn_def, ← tsum_mul_left]
    exact tsum_congr fun m => by rw [hg]; ring
  rw [h1, ← hsum.tsum_comm]
  exact tsum_congr h2

/-- `(-1 - z)^d`, viewed in `ℚ_p[[z]]`, is the image of the rational polynomial
`x^d ∘ (-1 - x)`. -/
private theorem neg_one_sub_X_pow_eq (d : ℕ) :
    (C (-1 : ℚ_[p]) + C (-1) * X) ^ d =
      ((((Polynomial.X ^ d : Polynomial ℚ).comp (-1 - Polynomial.X)).map
        (algebraMap ℚ ℚ_[p]) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
  simp [sub_eq_add_neg]

/-- **Reflection antisymmetry of `τ^an`.** For a prime `p ≥ 5` and `f ∈ ℚ_p⟨z⟩`,
`τ^an(f(-1 - z)) = -τ^an(f)`. -/
@[zeta5irr "lem_tau_an_reflect"]
theorem tauAn_tateSubst_neg_one_neg_one (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧}
    (hf : f ∈ tateAlgebra p) : tauAn (tateSubst (-1) (-1) f) = -tauAn f := by
  rw [tauAn_tateSubst hp5 hf (by simp) (by simp), tauAn_def, ← tsum_neg]
  refine tsum_congr fun d => ?_
  rw [neg_one_sub_X_pow_eq, tauAn_map_eq_tau, tau_comp_neg_one_sub_X, tau_X_pow_eq_kappa]
  push_cast
  ring

end Zeta5Irr
