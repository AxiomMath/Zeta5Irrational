/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.BTNormOne
public import Zeta5Irr.LocalFunctional.LocalDeltaConv

/-!
# `δ_R^ext` is norm-nonincreasing when the poles are `p`-adically separated

Let `R ⊆ ℤ` be finite and suppose that `r - r'` is a `p`-adic unit for all distinct
`r, r' ∈ R`. Then for every `f ∈ 𝒜 = ℚ_p⟨z⟩` the extended near-pole decomposition satisfies
`‖δ_R^ext(f)‖ ≤ ‖f‖`.

Indeed `δ_R^ext(f)` is the limit of `δ_R(f^{[D]})`, where `f^{[D]} = ∑_{d ≤ D} f_d z^d`. Each
truncation has Gauss norm `‖f^{[D]}‖ ≤ ‖f‖`, so `‖δ_R(f^{[D]})‖ ≤ ‖f‖` since `δ_R` is
norm-nonincreasing on polynomials, and the bound passes to the limit by continuity of the norm.

## Main results

* `Zeta5Irr.tateNorm_trunc_le`: `‖f^{[D]}‖ ≤ ‖f‖` for `f ∈ ℚ_p⟨z⟩`.
* `Zeta5Irr.norm_deltaExt_le_norm`: `‖δ_R^ext(f)‖ ≤ ‖f‖`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology PowerSeries

variable {p : ℕ} [Fact p.Prime] {R : Finset ℤ}

/-- Truncation does not increase the Gauss norm: for `f ∈ ℚ_p⟨z⟩` and every `n`,
`‖∑_{d < n} f_d z^d‖ ≤ ‖f‖`. -/
theorem tateNorm_trunc_le {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) (n : ℕ) :
    tateNorm (trunc n f : ℚ_[p]⟦X⟧) ≤ tateNorm f := by
  refine tateNorm_le_of_forall_norm_coeff_le fun d => ?_
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs
  · exact le_tateNorm hf d
  · simpa using tateNorm_nonneg f

/-- **`δ_R^ext` is norm-nonincreasing for `p`-adically separated poles.** If `R ⊆ ℤ` is finite
and `r - r'` is a `p`-adic unit for all distinct `r, r' ∈ R`, then
`‖δ_R^ext(f)‖ ≤ ‖f‖` for every `f ∈ ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_local_delta_norm"]
theorem norm_deltaExt_le_norm
    (hR : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → IsUnit ((r - r' : ℤ) : ℤ_[p])) (f : tateAlgebra p) :
    ‖deltaExt R (f : ℚ_[p]⟦X⟧)‖ ≤ ‖f‖ := by
  refine le_of_tendsto' (tendsto_deltaR_trunc_deltaExt (R := R) f.2).norm fun D => ?_
  refine (norm_deltaR_le_norm hR _).trans ?_
  rw [tateAlgebra.norm_def, tateAlgebra.coe_ofPolynomial, tateAlgebra.norm_def]
  exact tateNorm_trunc_le f.2 _

end Zeta5Irr
