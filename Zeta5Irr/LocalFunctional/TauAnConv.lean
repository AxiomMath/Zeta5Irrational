/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.KappaVal
public import Zeta5Irr.LocalFunctional.TauAn
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import Zeta5Irr.LocalFunctional.TauTate

/-!
# Convergence of the series defining `τ^an`

Let `p ≥ 5` be a prime and `f = ∑_{d ≥ 0} f_d z^d` an element of the Tate algebra
`𝒜 = ℚ_p⟨z⟩`. Then the series `∑_{d ≥ 0} f_d κ_d` converges in `ℚ_p`, so that `τ^an(f)` is its
sum.

Since `v_p(κ_d) ≥ -1`, we have `|κ_d|_p ≤ p`, hence `|f_d κ_d|_p ≤ p |f_d|_p → 0`. In the
complete non-archimedean field `ℚ_p`, a series whose terms tend to `0` converges.

## Main results

* `Zeta5Irr.norm_kappa_le`: `|κ_d|_p ≤ p` for every prime `p ≥ 5` and every `d`.
* `Zeta5Irr.summable_coeff_mul_kappa`: for `f ∈ ℚ_p⟨z⟩`, the series `∑_d f_d κ_d` is summable
  in `ℚ_p`.
* `Zeta5Irr.hasSum_coeff_mul_kappa_tauAn`: for `f ∈ ℚ_p⟨z⟩`, the series `∑_d f_d κ_d` has sum
  `τ^an(f)`.
* `Zeta5Irr.tendsto_sum_range_coeff_mul_kappa`: for `f ∈ ℚ_p⟨z⟩`, the partial sums
  `∑_{d < D} f_d κ_d` converge to `τ^an(f)`.

## Implementation notes

Convergence is stated as `Summable`, i.e. unconditional convergence in `ℚ_p`. This implies
convergence of the partial sums `∑_{d < D} f_d κ_d` (the form in the source), which is recorded
separately as `Zeta5Irr.tendsto_sum_range_coeff_mul_kappa`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p ≥ 5`, the weight `κ_d` satisfies `|κ_d|_p ≤ p`. -/
theorem norm_kappa_le (hp5 : 5 ≤ p) (d : ℕ) : ‖(kappa d : ℚ_[p])‖ ≤ p :=
  norm_ratCast_le_of_neg_one_le_padicValRat (neg_one_le_padicValRat_kappa hp5 d)

/-- **Convergence of `∑ f_d κ_d`.** For a prime `p ≥ 5` and `f ∈ ℚ_p⟨z⟩`, the series
`∑_{d ≥ 0} f_d κ_d` converges in `ℚ_p`. -/
@[zeta5irr "lem_tau_an_conv"]
theorem summable_coeff_mul_kappa (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    Summable fun d => coeff d f * (kappa d : ℚ_[p]) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have h := (mem_tateAlgebra_iff.mp hf).mul_const (p : ℝ)
  rw [zero_mul] at h
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_kappa_le hp5 d) (norm_nonneg _)

/-- For a prime `p ≥ 5` and `f ∈ ℚ_p⟨z⟩`, the series `∑_{d ≥ 0} f_d κ_d` has sum `τ^an(f)`. -/
theorem hasSum_coeff_mul_kappa_tauAn (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    HasSum (fun d => coeff d f * (kappa d : ℚ_[p])) (tauAn f) :=
  hasSum_tauAn (summable_coeff_mul_kappa hp5 hf)

/-- For a prime `p ≥ 5` and `f ∈ ℚ_p⟨z⟩`, the partial sums `∑_{d < D} f_d κ_d` converge to
`τ^an(f)` in `ℚ_p`. -/
theorem tendsto_sum_range_coeff_mul_kappa (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧}
    (hf : f ∈ tateAlgebra p) :
    Tendsto (fun D => ∑ d ∈ range D, coeff d f * (kappa d : ℚ_[p])) atTop (𝓝 (tauAn f)) :=
  (hasSum_coeff_mul_kappa_tauAn hp5 hf).tendsto_sum_nat

end Zeta5Irr
