/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDeltaext
public import Zeta5Irr.LocalFunctional.TauTateComplete
public import Zeta5Irr.LocalFunctional.LocalDeltaBound

/-!
# Convergence of the near-pole decompositions of truncations

Let `R ⊆ ℤ` be finite and `f ∈ 𝒜 = ℚ_p⟨z⟩`, with truncations `f^{[D]} = ∑_{d ≤ D} f_d z^d`.
Then the near-pole decompositions `δ_R(f^{[D]}) ∈ 𝓑_R` converge as `D → ∞`, so that the
limit defining `δ_R^ext(f)` exists.

For `D ≤ D'` every coefficient of `f^{[D']} - f^{[D]}` is `0` or a coefficient `f_d` with
`d > D`, so its Gauss norm is at most `sup_{d > D} |f_d|_p`, which tends to `0` since
`f ∈ 𝒜`. As `δ_R` is `ℚ_p`-linear and bounded, `‖δ_R(f^{[D']}) - δ_R(f^{[D]})‖` is at most
`C_R sup_{d > D} |f_d|_p`, so the sequence is Cauchy in `𝓑_R`. The space `𝓑_R` is complete,
being a finite product of the complete spaces `𝒜` and `ℚ_p` with the maximum norm.

## Main results

* `Zeta5Irr.tateAlgebra.completeSpace`: `ℚ_p⟨z⟩` is complete for its Gauss norm.
* `Zeta5Irr.deltaR_sub`: `δ_R(U - V) = δ_R(U) - δ_R(V)`.
* `Zeta5Irr.cauchySeq_deltaR_trunc`: the sequence `δ_R(f^{[D]})` is Cauchy in `𝓑_R`.
* `Zeta5Irr.exists_tendsto_deltaR_trunc`: the sequence `δ_R(f^{[D]})` converges in `𝓑_R`.
* `Zeta5Irr.tendsto_deltaR_trunc_deltaExt`: it converges to `δ_R^ext(f)`.

## Implementation notes

The truncation `f^{[D]}` is `PowerSeries.trunc (D + 1) f`, as in the definition of
`δ_R^ext`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology PowerSeries

variable {p : ℕ} [Fact p.Prime]

namespace tateAlgebra

/-- The Tate algebra `ℚ_p⟨z⟩` is complete for its Gauss norm. -/
instance completeSpace : CompleteSpace (tateAlgebra p) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨g, hg, hlim⟩ := exists_tendsto_tateNorm_sub_of_cauchy (f := fun i => (u i : ℚ_[p]⟦X⟧))
    (fun i => (u i).2) fun ε hε => by
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      refine ⟨N, fun i hi j hj => ?_⟩
      simpa only [dist_eq_norm, norm_def, Subalgebra.coe_sub] using hN i hi j hj
  refine ⟨⟨g, hg⟩, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  simpa [norm_def] using hlim

end tateAlgebra

variable {R : Finset ℤ}

/-- `δ_R` is additive with respect to subtraction: `δ_R(U - V) = δ_R(U) - δ_R(V)`. -/
theorem deltaR_sub (U V : Polynomial ℚ_[p]) : deltaR R (U - V) = deltaR R U - deltaR R V := by
  rw [eq_sub_iff_add_eq, ← deltaR_add, sub_add_cancel]

/-- For `f ∈ ℚ_p⟨z⟩`, the near-pole decompositions `δ_R(f^{[D]})` of the truncations
`f^{[D]} = ∑_{d ≤ D} f_d z^d` form a Cauchy sequence in `𝓑_R`. -/
theorem cauchySeq_deltaR_trunc {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    CauchySeq fun D : ℕ => deltaR R (trunc (D + 1) f) := by
  set C := max 1 (⨆ r : R,
    ‖(Polynomial.derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (mem_tateAlgebra_iff.mp hf) (ε / (2 * C))
    (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hcoeff : ∀ d, ‖(trunc (m + 1) f - trunc (n + 1) f).coeff d‖ ≤ ε / (2 * C) := by
    intro d
    have key : ∀ k ≥ N, d ∉ Finset.range (k + 1) → ‖coeff d f‖ ≤ ε / (2 * C) := by
      intro k hk hd
      simpa using (hN d (by simp at hd; omega)).le
    rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc]
    have hpos : 0 ≤ ε / (2 * C) := by positivity
    split_ifs with h1 h2 h2
    · simp [hpos]
    · simpa using key n hn (by simpa using h2)
    · simpa using key m hm (by simpa using h1)
    · simp [hpos]
  rw [dist_eq_norm, ← deltaR_sub]
  refine (norm_deltaR_le _).trans_lt ?_
  have hnorm : ‖tateAlgebra.ofPolynomial p (trunc (m + 1) f - trunc (n + 1) f)‖ ≤
      ε / (2 * C) := by
    rw [tateAlgebra.norm_def, tateAlgebra.coe_ofPolynomial]
    exact tateNorm_coe_le_of_forall_norm_coeff_le hcoeff
  calc C * ‖tateAlgebra.ofPolynomial p (trunc (m + 1) f - trunc (n + 1) f)‖
      ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left hnorm hC.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- **The limit defining `δ_R^ext` exists.** For a finite set `R ⊆ ℤ` and `f ∈ ℚ_p⟨z⟩`, the
near-pole decompositions `δ_R(f^{[D]})` of the truncations `f^{[D]} = ∑_{d ≤ D} f_d z^d`
converge in `𝓑_R` as `D → ∞`. -/
@[zeta5irr "lem_local_delta_conv"]
theorem exists_tendsto_deltaR_trunc {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    ∃ l, Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete (cauchySeq_deltaR_trunc hf)

/-- For `f ∈ ℚ_p⟨z⟩`, the near-pole decompositions `δ_R(f^{[D]})` of the truncations converge
to `δ_R^ext(f)`. -/
theorem tendsto_deltaR_trunc_deltaExt {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    Tendsto (fun D : ℕ => deltaR R (trunc (D + 1) f)) atTop (𝓝 (deltaExt R f)) :=
  tendsto_deltaExt (exists_tendsto_deltaR_trunc hf)

end Zeta5Irr
