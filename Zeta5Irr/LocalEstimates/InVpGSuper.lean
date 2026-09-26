/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG

/-!
# Supermultiplicativity of the Gauss valuation `v_p^G`

For `A, B ∈ ℚ_p[X]` we have `v_p^G(AB) ≥ v_p^G(A) + v_p^G(B)`. The coefficient of `X^n` in
`AB` is `∑_{k + l = n} a_k b_l`; each summand has valuation `v_p(a_k) + v_p(b_l)`, which is at
least `v_p^G(A) + v_p^G(B)`, and the valuation of a finite sum is at least the minimum of the
valuations of its terms. Taking the minimum over `n` gives the claim.

## Main results

* `Zeta5Irr.add_le_gaussAddVal_mul`: `gaussAddVal v A + gaussAddVal v B ≤ gaussAddVal v (A * B)`
  for any additive valuation `v` on a ring.
* `Zeta5Irr.add_le_vpG_mul`: `vpG A + vpG B ≤ vpG (A * B)`.

## Implementation notes

The inequality holds for the Gauss valuation attached to any additive valuation on any ring;
the statement for `ℚ_p[X]` is its `p`-adic case. Over `ℚ_p` it is in fact an equality (Gauss's
lemma), but only the inequality is needed here. When `A = 0` or `B = 0` both sides are `⊤`,
so no case split is needed in the proof.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.1 (Valuation and determinant preliminaries).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

section General

variable {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]

/-- The Gauss valuation attached to an additive valuation is supermultiplicative:
`gaussAddVal v A + gaussAddVal v B ≤ gaussAddVal v (A * B)`. -/
theorem add_le_gaussAddVal_mul (v : AddValuation R Γ) (A B : R[X]) :
    gaussAddVal v A + gaussAddVal v B ≤ gaussAddVal v (A * B) := by
  refine (le_gaussAddVal_iff v).mpr fun n => ?_
  rw [coeff_mul]
  refine AddValuation.map_le_sum v fun x _ => ?_
  rw [v.map_mul]
  exact add_le_add (gaussAddVal_le v A x.1) (gaussAddVal_le v B x.2)

end General

variable {p : ℕ} [Fact p.Prime]

/-- Supermultiplicativity of the Gauss valuation on `ℚ_p[X]`:
`v_p^G(AB) ≥ v_p^G(A) + v_p^G(B)`. -/
@[zeta5irr "lem_in_vpG_super"]
theorem add_le_vpG_mul (A B : ℚ_[p][X]) : vpG A + vpG B ≤ vpG (A * B) :=
  add_le_gaussAddVal_mul _ A B

end Zeta5Irr
