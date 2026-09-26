/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDist
public import Zeta5Irr.LocalEstimates.InScale

/-!
# Homogeneity of the distributed functional `𝒯_p(-; R)`

Let `p` be a prime and `R ⊆ ℤ` finite. The distributed functional
`𝒯_p(A; R) = p^{-4} ∑_{a=0}^{p-1} τ_{Y_p}^ext(δ_{R_a}^ext(p^{-#R} A(a + pz) ∏_{s ∈ Σ_a} ε_s))`
is `ℚ`-homogeneous in `A ∈ ℚ[x]`: `𝒯_p(cA; R) = c 𝒯_p(A; R)` for `c ∈ ℚ`.

Each map composed in `𝒯_p` commutes with scalars: the substitution `A ↦ A(a + pz)`,
multiplication by the fixed series `p^{-#R} ∏_{s ∈ Σ_a} ε_s`, and the composite
`τ_Y^ext ∘ δ_R^ext`, which is homogeneous on every power series.

## Main results

* `Zeta5Irr.tauDist_smul`: `𝒯_p(c A; R) = c 𝒯_p(A; R)` for `c ∈ ℚ`.

## Implementation notes

Homogeneity of `τ_Y^ext ∘ δ_R^ext` holds for every power series, not only on the Tate algebra,
so no convergence hypothesis is needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **Homogeneity of `𝒯_p`.** For every prime `p`, finite `R ⊆ ℤ`, `c ∈ ℚ` and `A ∈ ℚ[x]`,
`𝒯_p(c A; R) = c 𝒯_p(A; R)`. -/
@[zeta5irr "lem_tau_dist_smul"]
theorem tauDist_smul (R : Finset ℤ) (c : ℚ) (A : ℚ[X]) :
    tauDist p R (c • A) = c • tauDist p R A := by
  rw [← algebraMap_smul ℚ_[p] c (tauDist p R A)]
  simp only [tauDist, Finset.smul_sum, smul_comm (algebraMap ℚ ℚ_[p] c) ((p : ℚ_[p]) ^ 4)⁻¹]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ?_
  rw [← tauExt_deltaExt_smul]
  congr 2
  rw [smul_comp, Polynomial.map_smul, Polynomial.coe_smul, smul_mul_assoc, smul_comm]

end Zeta5Irr
