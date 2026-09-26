/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InVpGSuper

/-!
# Supermultiplicativity of the Gauss valuation `v_p^G` (§4.4)

For `A₁, A₂ ∈ ℚ_p[X]` we have `v_p^G(A₁ A₂) ≥ v_p^G(A₁) + v_p^G(A₂)`.

## Main results

* `Zeta5Irr.add_le_vpG_mul'`: `vpG A₁ + vpG A₂ ≤ vpG (A₁ * A₂)`.

## Implementation notes

The blueprint states this inequality twice: here in §4.4 (`lem_local_vpG_mul`) and again in §5.1
(`lem_in_vpG_super`), where it is proved as `Zeta5Irr.add_le_vpG_mul`. This file only restates
that lemma under the §4.4 label so that each blueprint entity has its own tagged declaration.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The Gauss valuation on `ℚ_p[X]` is supermultiplicative:
`v_p^G(A₁ A₂) ≥ v_p^G(A₁) + v_p^G(A₂)`. -/
@[zeta5irr "lem_local_vpG_mul"]
theorem add_le_vpG_mul' (A₁ A₂ : ℚ_[p][X]) : vpG A₁ + vpG A₂ ≤ vpG (A₁ * A₂) :=
  add_le_vpG_mul A₁ A₂

end Zeta5Irr
