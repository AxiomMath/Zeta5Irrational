/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauTate

/-!
# Submultiplicativity of the Gauss norm on `ℚ_p⟨z⟩`

For `f, g ∈ 𝒜 = ℚ_p⟨z⟩`, the product `fg` formed in `ℚ_p[[z]]` again lies in `𝒜`, and the
Gauss norm is submultiplicative: `‖fg‖ ≤ ‖f‖ ‖g‖`. The coefficient of `z^k` in `fg` is the
finite sum `∑_{i+j=k} f_i g_j`, which the ultrametric inequality bounds by
`max_{i+j=k} |f_i|_p |g_j|_p ≤ ‖f‖ ‖g‖`.

## Main results

* `Zeta5Irr.mul_mem_tateAlgebra`: `ℚ_p⟨z⟩` is closed under multiplication in `ℚ_[p]⟦X⟧`.
* `Zeta5Irr.tateNorm_mul_le`: `‖fg‖ ≤ ‖f‖ ‖g‖` for `f, g ∈ ℚ_p⟨z⟩`.

## Implementation notes

Closure under multiplication is part of `ℚ_p⟨z⟩` being a subalgebra (Mathlib's
`PowerSeries.IsRestricted.subring`), and the norm bound is the specialisation of Mathlib's
`MvPowerSeries.gaussNorm_mul_le` to radius `1` and the `p`-adic norm, which is multiplicative
and non-archimedean.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4: completion at a prime.
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The product in `ℚ_[p]⟦X⟧` of two elements of `ℚ_p⟨z⟩` lies in `ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_tau_tate_mul"]
theorem mul_mem_tateAlgebra {f g : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p)
    (hg : g ∈ tateAlgebra p) : f * g ∈ tateAlgebra p :=
  (tateAlgebra p).mul_mem hf hg

/-- The Gauss norm is submultiplicative on `ℚ_p⟨z⟩`: `‖fg‖ ≤ ‖f‖ ‖g‖`. -/
@[zeta5irr "lem_tau_tate_mul"]
theorem tateNorm_mul_le {f g : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) (hg : g ∈ tateAlgebra p) :
    tateNorm (f * g) ≤ tateNorm f * tateNorm g :=
  MvPowerSeries.gaussNorm_mul_le _ _ f g (fun _ => zero_le_one) (fun _ => norm_nonneg _)
    (fun a b => (norm_mul a b).le) (fun a b => IsUltrametricDist.norm_add_le_max a b) norm_zero
    (hasGaussNorm hf).hasMvGaussNorm (hasGaussNorm hg).hasMvGaussNorm

end Zeta5Irr
