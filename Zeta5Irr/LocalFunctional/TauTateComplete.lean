/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauTate

/-!
# Completeness of the Tate algebra `ℚ_p⟨z⟩`

The Tate algebra `𝒜 = ℚ_p⟨z⟩` is complete for its Gauss norm `‖f‖ = sup_d |f_d|_p`: every
sequence `(f⁽ⁱ⁾)` in `𝒜` which is Cauchy for `‖·‖` converges in `‖·‖` to some `f ∈ 𝒜`.

The proof is coefficientwise. Since `|f_d| ≤ ‖f‖` on `𝒜`, each coefficient sequence
`(f⁽ⁱ⁾_d)_i` is Cauchy in `ℚ_p`, hence converges to some `f_d`. A Cauchy bound
`‖f⁽ⁱ⁾ - f⁽ⁱ'⁾‖ ≤ ε` passes to the limit `i' → ∞` coefficientwise, giving
`|f⁽ⁱ⁾_d - f_d| ≤ ε` uniformly in `d`; this shows both that `|f_d| → 0` and that
`‖f⁽ⁱ⁾ - f‖ → 0`.

## Main results

* `Zeta5Irr.exists_tendsto_tateNorm_sub_of_cauchy`: a sequence in `ℚ_p⟨z⟩` which is Cauchy for
  the Gauss norm converges in the Gauss norm to an element of `ℚ_p⟨z⟩`.

## Implementation notes

`ℚ_p⟨z⟩` is a subalgebra of `ℚ_[p]⟦X⟧` and the Gauss norm is a real-valued function on power
series, not a `Norm` instance, so completeness is stated directly in terms of Cauchy sequences
for `tateNorm` rather than as a `CompleteSpace` instance.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- **Completeness of `ℚ_p⟨z⟩`.** A sequence of elements of the Tate algebra `ℚ_p⟨z⟩` which is
Cauchy for the Gauss norm converges in the Gauss norm to an element of `ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_tau_tate_complete"]
theorem exists_tendsto_tateNorm_sub_of_cauchy {f : ℕ → ℚ_[p]⟦X⟧}
    (hf : ∀ i, f i ∈ tateAlgebra p)
    (hc : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, tateNorm (f i - f j) < ε) :
    ∃ g ∈ tateAlgebra p, Tendsto (fun i => tateNorm (f i - g)) atTop (𝓝 0) := by
  have hcoeff : ∀ i j d, ‖coeff d (f i) - coeff d (f j)‖ ≤ tateNorm (f i - f j) := fun i j d => by
    simpa using le_tateNorm (sub_mem (hf i) (hf j)) d
  have hcauchy : ∀ d, CauchySeq fun i => coeff d (f i) := by
    intro d
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun i hi => ?_⟩
    rw [dist_eq_norm]
    exact (hcoeff i N d).trans_lt (hN i hi N le_rfl)
  choose a ha using fun d => cauchySeq_tendsto_of_complete (hcauchy d)
  set g : ℚ_[p]⟦X⟧ := PowerSeries.mk a with hg
  have hcg : ∀ d, coeff d g = a d := fun d => by simp [hg]
  have hunif : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ d, ‖coeff d (f i) - a d‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun i hi d => ?_⟩
    have hlim : Tendsto (fun j => ‖coeff d (f i) - coeff d (f j)‖) atTop
        (𝓝 ‖coeff d (f i) - a d‖) :=
      ((tendsto_const_nhds.sub (ha d)).norm)
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with j hj
    exact ((hcoeff i j d).trans_lt (hN i hi j hj)).le
  refine ⟨g, ?_, ?_⟩
  · rw [mem_tateAlgebra_iff, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    obtain ⟨D, hD⟩ := Metric.tendsto_atTop.mp (mem_tateAlgebra_iff.mp (hf N)) (ε / 2)
      (half_pos hε)
    refine ⟨D, fun d hd => ?_⟩
    have h1 := hD d hd
    rw [dist_zero_right, norm_norm] at h1
    rw [dist_zero_right, norm_norm, hcg]
    linarith [norm_le_norm_add_norm_sub' (a d) (coeff d (f N)), norm_sub_rev (a d) (coeff d (f N)),
      hN N le_rfl d]
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    refine ⟨N, fun i hi => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tateNorm_nonneg _)]
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    exact tateNorm_le_of_forall_norm_coeff_le fun d => by simpa [hcg] using hN i hi d

end Zeta5Irr
