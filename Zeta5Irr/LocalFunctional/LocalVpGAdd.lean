/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG

/-!
# The ultrametric inequality for the Gauss valuation `v_p^G`

For `A₁, A₂ ∈ ℚ_p[X]` we have `v_p^G(A₁ + A₂) ≥ min (v_p^G(A₁), v_p^G(A₂))`. The coefficient
of `X^k` in `A₁ + A₂` is the sum of the coefficients of `X^k` in `A₁` and `A₂`, whose `p`-adic
valuation is at least the minimum of theirs; taking the minimum over `k` gives the claim.

## Main results

* `Zeta5Irr.min_le_vpG_add`: `min (vpG A₁) (vpG A₂) ≤ vpG (A₁ + A₂)`.

## Implementation notes

The inequality holds for the Gauss valuation attached to any additive valuation; this is
`Zeta5Irr.min_le_gaussAddVal_add`, of which the statement here is the `p`-adic case.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The ultrametric inequality for the Gauss valuation on `ℚ_p[X]`:
`v_p^G(A₁ + A₂) ≥ min (v_p^G(A₁), v_p^G(A₂))`. -/
@[zeta5irr "lem_local_vpG_add"]
theorem min_le_vpG_add (A₁ A₂ : ℚ_[p][X]) : min (vpG A₁) (vpG A₂) ≤ vpG (A₁ + A₂) :=
  min_le_gaussAddVal_add _ A₁ A₂

end Zeta5Irr
