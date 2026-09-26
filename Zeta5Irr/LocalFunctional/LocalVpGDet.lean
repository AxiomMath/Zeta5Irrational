/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG
public import Zeta5Irr.LocalEstimates.InDetWeights

/-!
# A lower bound for the Gauss valuation of a determinant

Let `M` be an `m × m` matrix with entries in `ℚ_p[X]` and let `c ∈ ℤ` with `v_p^G(M_{ij}) ≥ c`
for all `i, j`. Then `v_p^G(det M) ≥ m c`.

By the Leibniz formula, `det M = ∑_σ ε(σ) ∏_j M_{σ(j), j}`. By supermultiplicativity of the
Gauss valuation each product has valuation at least `m c`, a sign does not change the Gauss
valuation, and the Gauss valuation of a finite sum is at least the minimum of the Gauss
valuations of its terms.

## Main results

* `Zeta5Irr.card_nsmul_le_gaussAddVal_det`: the bound for the Gauss valuation attached to an
  additive valuation `v` on a commutative ring, with `c` in the value monoid of `v`.
* `Zeta5Irr.card_mul_le_vpG_det`: the bound `v_p^G(det M) ≥ m c` over `ℚ_p[X]`.

## Implementation notes

The matrix is indexed by an arbitrary finite type `ι` of cardinality `m` rather than by
`{1, …, m}`, and the hypothesis `m ≥ 1` is not needed: for the empty index set the determinant
is `1`, of Gauss valuation `0 = m c`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

section General

variable {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]

/-- Let `M` be a square matrix over `R[X]`, indexed by a finite type `ι`, all of whose entries
have Gauss valuation at least `c`. Then `det M` has Gauss valuation at least `card ι • c`. -/
theorem card_nsmul_le_gaussAddVal_det (v : AddValuation R Γ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R[X]) (c : Γ) (hM : ∀ i j, c ≤ gaussAddVal v (M i j)) :
    Fintype.card ι • c ≤ gaussAddVal v M.det := by
  refine le_gaussAddVal_det_of_forall_perm v M _ fun σ => ?_
  rw [← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun j _ => hM (σ j) j

end General

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **Gauss valuation of a determinant.** Let `M` be an `m × m` matrix with entries in
`ℚ_p[X]` and `c ∈ ℤ` with `v_p^G(M_{ij}) ≥ c` for all `i, j`. Then `v_p^G(det M) ≥ m c`. -/
@[zeta5irr "lem_local_vpG_det"]
theorem card_mul_le_vpG_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[p][X]) (c : ℤ) (hM : ∀ i j, (c : WithTop ℤ) ≤ vpG (M i j)) :
    ((Fintype.card ι * c : ℤ) : WithTop ℤ) ≤ vpG M.det := by
  have := card_nsmul_le_gaussAddVal_det Padic.addValuation M (c : WithTop ℤ) hM
  rwa [← WithTop.coe_nsmul, nsmul_eq_mul] at this

end Padic

end Zeta5Irr
