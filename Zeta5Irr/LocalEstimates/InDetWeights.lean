/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG
public import Zeta5Irr.LocalEstimates.InVpGSuper
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# A determinant bound from row and column weights

Let `B` be a square matrix with entries in `ℚ_p[X]` and let `w_r` be rational weights with
`v_p^G(B_{rs}) ≥ w_r + w_s` for all indices `r, s`. Then `v_p^G(det B) ≥ 2 ∑_r w_r`.

The determinant is `∑_σ ε(σ) ∏_r B_{σ(r), r}`. By supermultiplicativity of the Gauss valuation
each product has valuation at least `∑_r (w_{σ(r)} + w_r) = 2 ∑_r w_r`, a sign does not change
the Gauss valuation, and the Gauss valuation of a finite sum is at least the minimum of the
Gauss valuations of its terms.

## Main results

* `Zeta5Irr.le_gaussAddVal_det_of_forall_perm`: the Leibniz bound: a lower bound for the Gauss
  valuation of every diagonal product along a permutation bounds that of the determinant.
* `Zeta5Irr.two_nsmul_sum_le_gaussAddVal_det`: the bound for the Gauss valuation attached to
  an additive valuation `v` on a commutative ring, with weights in the value monoid of `v`.
* `Zeta5Irr.gaussAddVal_map`: the Gauss valuation commutes with pushing the valuation forward
  along a `⊤`-preserving ordered additive homomorphism.
* `Zeta5Irr.two_mul_sum_le_vpG_det`: the bound `v_p^G(det B) ≥ 2 ∑_r w_r` over `ℚ_p[X]` with
  rational weights.

## Implementation notes

* The index set is an arbitrary finite type rather than `{1, …, h}` with `h ≥ 1`; the
  hypothesis `h ≥ 1` is not needed (for the empty index set both sides are `0`).
* The Gauss valuation `v_p^G` takes values in `ℤ ∪ {+∞}` while the weights are rational, so
  the comparison is made in `ℚ ∪ {+∞}`, after mapping `v_p^G` along the inclusion
  `ℤ ∪ {+∞} → ℚ ∪ {+∞}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.1 (Valuation and determinant preliminaries).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

section General

variable {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]

/-- The Gauss valuation of a finite product is at least the sum of the Gauss valuations. -/
theorem sum_le_gaussAddVal_prod (v : AddValuation R Γ) {ι : Type*} (s : Finset ι)
    (f : ι → R[X]) : ∑ i ∈ s, gaussAddVal v (f i) ≤ gaussAddVal v (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, ← C_1, gaussAddVal_C, v.map_one, le_refl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (add_le_add_right ih _).trans (add_le_gaussAddVal_mul v _ _)

/-- **Leibniz bound.** If for every permutation `σ` the sum of the Gauss valuations of the
entries `B (σ r) r` is at least `c`, then `c ≤ gaussAddVal v (det B)`. -/
theorem le_gaussAddVal_det_of_forall_perm (v : AddValuation R Γ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Matrix ι ι R[X]) (c : Γ)
    (hB : ∀ σ : Equiv.Perm ι, c ≤ ∑ r, gaussAddVal v (B (σ r) r)) :
    c ≤ gaussAddVal v B.det := by
  rw [Matrix.det_apply']
  refine le_trans (Finset.le_inf fun σ _ => ?_) (finset_inf_le_gaussAddVal_sum v _ _)
  have hsign : gaussAddVal v ((Equiv.Perm.sign σ : ℤ) * ∏ r, B (σ r) r) =
      gaussAddVal v (∏ r, B (σ r) r) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hsign]
  exact (hB σ).trans (sum_le_gaussAddVal_prod v _ _)

/-- Let `B` be a square matrix over `R[X]` and `w` a family of weights with
`w r + w s ≤ gaussAddVal v (B r s)` for all `r, s`. Then `2 • ∑ r, w r ≤ gaussAddVal v (det B)`. -/
theorem two_nsmul_sum_le_gaussAddVal_det (v : AddValuation R Γ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (B : Matrix ι ι R[X]) (w : ι → Γ)
    (hB : ∀ r s, w r + w s ≤ gaussAddVal v (B r s)) :
    2 • ∑ r, w r ≤ gaussAddVal v B.det := by
  refine le_gaussAddVal_det_of_forall_perm v B _ fun σ => ?_
  calc 2 • ∑ r, w r = ∑ r, (w (σ r) + w r) := by
        rw [Finset.sum_add_distrib, Equiv.sum_comp σ w, two_nsmul]
    _ ≤ ∑ r, gaussAddVal v (B (σ r) r) := Finset.sum_le_sum fun r _ => hB (σ r) r

variable {Γ' : Type*} [LinearOrderedAddCommMonoidWithTop Γ']

/-- The Gauss valuation attached to the pushforward `v.map f` of `v` along a `⊤`-preserving
ordered additive homomorphism `f` is `f` applied to the Gauss valuation attached to
`v`. -/
theorem gaussAddVal_map (v : AddValuation R Γ) (f : Γ →+o Γ') (ht : f ⊤ = ⊤) (A : R[X]) :
    gaussAddVal (AddValuation.map f ht v) A = f (gaussAddVal v A) := by
  by_cases hA : A = 0
  · simp [hA, ht]
  obtain ⟨i, -, hi⟩ := exists_gaussAddVal_eq v hA
  refine le_antisymm ?_ ((le_gaussAddVal_iff _).mpr fun j => ?_)
  · exact (gaussAddVal_le _ A i).trans (by rw [hi]; rfl)
  · exact f.monotone' (gaussAddVal_le v A j)

end General

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **Determinant bound from row and column weights.** Let `B` be a square matrix with entries
in `ℚ_p[X]` and `w` a family of rational weights with `v_p^G(B_{rs}) ≥ w_r + w_s` for all
`r, s`. Then `v_p^G(det B) ≥ 2 ∑_r w_r`. The Gauss valuations are compared with rationals
after mapping `ℤ ∪ {+∞}` into `ℚ ∪ {+∞}`. -/
@[zeta5irr "lem_in_det_weights"]
theorem two_mul_sum_le_vpG_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℚ_[p][X]) (w : ι → ℚ)
    (hB : ∀ r s, ((w r + w s : ℚ) : WithTop ℚ) ≤ (vpG (B r s)).map ((↑) : ℤ → ℚ)) :
    ((2 * ∑ r, w r : ℚ) : WithTop ℚ) ≤ (vpG B.det).map ((↑) : ℤ → ℚ) := by
  let f : WithTop ℤ →+o WithTop ℚ :=
    { (Int.castAddHom ℚ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr Int.cast_mono }
  have ht : f ⊤ = ⊤ := rfl
  have hfx : ∀ x, f x = x.map ((↑) : ℤ → ℚ) := fun _ => rfl
  have key := two_nsmul_sum_le_gaussAddVal_det (AddValuation.map f ht Padic.addValuation) B
    (fun r => (w r : WithTop ℚ)) fun r s => by
      simpa only [gaussAddVal_map, hfx, ← WithTop.coe_add] using hB r s
  rw [gaussAddVal_map, hfx, ← WithTop.coe_sum, ← WithTop.coe_nsmul, two_nsmul] at key
  rwa [two_mul]

end Padic

end Zeta5Irr
