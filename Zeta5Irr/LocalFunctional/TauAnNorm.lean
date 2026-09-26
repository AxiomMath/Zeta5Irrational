/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauAnConv

/-!
# The norm bound `|τ^an(f)|_p ≤ p ‖f‖`

Let `p ≥ 5` be a prime and `f = ∑_{d ≥ 0} f_d z^d` an element of the Tate algebra
`𝒜 = ℚ_p⟨z⟩`, with Gauss norm `‖f‖ = sup_d |f_d|_p`. Then the analytic functional satisfies
`|τ^an(f)|_p ≤ p ‖f‖`; that is, `τ^an : 𝒜 → ℚ_p` is bounded of operator norm at most `p`.

Each term of the series `τ^an(f) = ∑_d f_d κ_d` satisfies
`|f_d κ_d|_p ≤ p |f_d|_p ≤ p ‖f‖`, since `|κ_d|_p ≤ p`. By the ultrametric inequality the same
bound holds for the sum.

## Main results

* `Zeta5Irr.norm_tauAn_le`: for `f ∈ ℚ_p⟨z⟩`, `‖τ^an(f)‖ ≤ p * ‖f‖`.

## Implementation notes

The source bounds each partial sum by the ultrametric inequality and passes to the limit.
Here the bound is obtained in one step from the ultrametric estimate for an unconditional sum
in `ℚ_p`, which bounds the norm of the sum by any common bound on the norms of the terms.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- **Norm bound for `τ^an`.** For a prime `p ≥ 5` and `f ∈ ℚ_p⟨z⟩`,
`|τ^an(f)|_p ≤ p ‖f‖`, where `‖f‖` is the Gauss norm. -/
@[zeta5irr "lem_tau_an_norm"]
theorem norm_tauAn_le (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    ‖tauAn f‖ ≤ p * tateNorm f := by
  rw [tauAn_def]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun d => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (norm_kappa_le hp5 d) (le_tateNorm hf d) (norm_nonneg _) (by positivity)

end Zeta5Irr
