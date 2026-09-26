/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauTateComplete
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Convergence of `∑ p^j U_j` in the Tate algebra

Let `p` be a prime and `U_j ∈ ℤ_p[z]` for `j ≥ 0`. Then the series `∑_{j ≥ 0} p^j U_j`
converges in the Tate algebra `𝒜 = ℚ_p⟨z⟩` for its Gauss norm.

The partial sums are polynomials, hence lie in `𝒜`. Since `‖U_j‖ ≤ 1`, the ultrametric
inequality gives `‖∑_{j=J}^{J'-1} p^j U_j‖ ≤ p^{-J}`, so the partial sums are Cauchy, and `𝒜`
is complete. More generally, in `𝒜` any series whose terms tend to `0` converges.

## Main results

* `Zeta5Irr.tateNorm_sum_le`: the ultrametric inequality for finite sums in `ℚ_p⟨z⟩`.
* `Zeta5Irr.exists_tendsto_tateNorm_sum_sub_of_tendsto`: in `ℚ_p⟨z⟩`, a series whose terms
  tend to `0` in the Gauss norm converges in the Gauss norm to an element of `ℚ_p⟨z⟩`.
* `Zeta5Irr.exists_tendsto_tateNorm_sum_pow_smul_sub`: for `U_j ∈ ℤ_p[z]`, the series
  `∑_j p^j U_j` converges in `ℚ_p⟨z⟩`.

## Implementation notes

Convergence is stated, as for the completeness of `ℚ_p⟨z⟩`, as the existence of `g ∈ ℚ_p⟨z⟩`
with `‖∑_{j < J} p^j U_j - g‖ → 0` as `J → ∞`. A polynomial `U ∈ ℤ_p[z]` is regarded as an
element of `ℚ_p⟨z⟩` by mapping its coefficients to `ℚ_p` and then viewing it as a power series.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

/-- The ultrametric inequality for finite sums in `ℚ_p⟨z⟩`: if every term has Gauss norm at
most `ε ≥ 0`, then so does the sum. -/
theorem tateNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → ℚ_[p]⟦X⟧}
    (hf : ∀ i ∈ s, f i ∈ tateAlgebra p) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i ∈ s, tateNorm (f i) ≤ ε) : tateNorm (∑ i ∈ s, f i) ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε
  | insert a s ha ih =>
    rw [sum_insert ha]
    refine (tateNorm_add_le_max (hf a (mem_insert_self a s))
      (sum_mem fun i hi => hf i (mem_insert_of_mem hi))).trans (max_le ?_ ?_)
    · exact h a (mem_insert_self a s)
    · exact ih (fun i hi => hf i (mem_insert_of_mem hi)) fun i hi => h i (mem_insert_of_mem hi)

/-- In `ℚ_p⟨z⟩`, a series whose terms tend to `0` in the Gauss norm converges: its partial sums
converge in the Gauss norm to an element of `ℚ_p⟨z⟩`. -/
theorem exists_tendsto_tateNorm_sum_sub_of_tendsto {f : ℕ → ℚ_[p]⟦X⟧}
    (hf : ∀ j, f j ∈ tateAlgebra p) (h0 : Tendsto (fun j => tateNorm (f j)) atTop (𝓝 0)) :
    ∃ g ∈ tateAlgebra p,
      Tendsto (fun J => tateNorm (∑ j ∈ range J, f j - g)) atTop (𝓝 0) := by
  refine exists_tendsto_tateNorm_sub_of_cauchy (fun J => sum_mem fun j _ => hf j) ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h0 (ε / 2) (half_pos hε)
  have hN' : ∀ j ≥ N, tateNorm (f j) ≤ ε / 2 := fun j hj => by
    have := hN j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tateNorm_nonneg _)] at this
    exact this.le
  -- the estimate for `i ≤ j`
  have key : ∀ i j, N ≤ i → i ≤ j →
      tateNorm (∑ k ∈ range j, f k - ∑ k ∈ range i, f k) ≤ ε / 2 := by
    intro i j hi hij
    rw [← sum_Ico_eq_sub _ hij]
    exact tateNorm_sum_le (fun k _ => hf k) (half_pos hε).le
      fun k hk => hN' k (hi.trans (mem_Ico.mp hk).1)
  refine ⟨N, fun i hi j hj => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  rcases le_total i j with hij | hji
  · rw [← tateNorm_neg, neg_sub]
    exact key i j hi hij
  · exact key j i hj hji

/-- **Convergence of `∑ p^j U_j` in `ℚ_p⟨z⟩`.** For polynomials `U_j ∈ ℤ_p[z]`, the partial
sums of the series `∑_{j ≥ 0} p^j U_j` converge in the Gauss norm to an element of the Tate
algebra `ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_local_series_conv"]
theorem exists_tendsto_tateNorm_sum_pow_smul_sub (U : ℕ → Polynomial ℤ_[p]) :
    ∃ g ∈ tateAlgebra p, Tendsto (fun J => tateNorm
      (∑ j ∈ range J, (p : ℚ_[p]) ^ j • (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) :
        ℚ_[p]⟦X⟧) - g)) atTop (𝓝 0) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine exists_tendsto_tateNorm_sum_sub_of_tendsto
    (fun j => Subalgebra.smul_mem _ (coe_mem_tateAlgebra _) _) ?_
  have hlim : Tendsto (fun j : ℕ => ((p : ℝ)⁻¹) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp)
  refine squeeze_zero (fun j => tateNorm_nonneg _) (fun j => ?_) hlim
  rw [tateNorm_smul, norm_pow, Padic.norm_p, inv_pow]
  calc ((p : ℝ) ^ j)⁻¹ * _ ≤ ((p : ℝ) ^ j)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (tateNorm_map_coe_le_one (U j)) (by positivity)
    _ = _ := mul_one _

end Zeta5Irr
