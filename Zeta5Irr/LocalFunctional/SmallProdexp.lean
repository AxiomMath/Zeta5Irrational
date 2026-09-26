/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Valuation of a product of principal units minus one

Let `p` be a prime, `Λ` a finite nonempty set and `η_ι ∈ ℚ_p` with `v_p(η_ι) ≥ 1`. Then
`v_p(∏_{ι ∈ Λ} (1 + η_ι) - 1) ≥ min_{ι ∈ Λ} v_p(η_ι)`.

The proof is by induction on `Λ`: writing `Λ = {ι₀} ∪ Λ₁`,
`∏_Λ (1 + η_ι) - 1 = (1 + η_{ι₀}) (∏_{Λ₁} (1 + η_ι) - 1) + η_{ι₀}`, where
`v(1 + η_{ι₀}) ≥ 0`, and the ultrametric inequality concludes.

## Main results

* `Zeta5Irr.finset_inf_le_addValuation_prod_one_add_sub_one`: for any additive valuation `v`
  on a commutative ring and any finite family `η` with `0 ≤ v (η ι)`,
  `s.inf (v ∘ η) ≤ v (∏ ι ∈ s, (1 + η ι) - 1)`.
* `Zeta5Irr.inf'_le_padicAddValuation_prod_one_add_sub_one`: the `p`-adic statement of the
  blueprint, with `v_p(η_ι) ≥ 1` and the minimum over a nonempty index set.

## Implementation notes

The argument only uses `v(1 + η_ι) ≥ 0`, which already follows from `v(η_ι) ≥ 0` by the
ultrametric inequality, so the general statement assumes `0 ≤ v(η_ι)` rather than
`1 ≤ v(η_ι)`. With `Finset.inf` in place of the minimum, it also holds for `Λ = ∅`, both sides
being `⊤`. The ultrametric inequality is applied to the constants directly, as
`AddValuation.map_add`, rather than through the Gauss valuation of constant polynomials.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

namespace Zeta5Irr

section General

variable {R Γ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]

/-- For an additive valuation `v` and a finite family `η` with `0 ≤ v (η ι)`, the valuation of
`∏ ι ∈ s, (1 + η ι) - 1` is at least the minimum of the valuations `v (η ι)`. -/
theorem finset_inf_le_addValuation_prod_one_add_sub_one {ι : Type*} (v : AddValuation R Γ)
    (s : Finset ι) {η : ι → R} (hη : ∀ i ∈ s, 0 ≤ v (η i)) :
    s.inf (fun i => v (η i)) ≤ v (∏ i ∈ s, (1 + η i) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ih := ih fun i hi => hη i (Finset.mem_insert_of_mem hi)
    have ha0 : 0 ≤ v (1 + η a) :=
      le_trans (le_min (by simp) (hη a (Finset.mem_insert_self a s))) (v.map_add _ _)
    have key : ∏ i ∈ insert a s, (1 + η i) - 1 =
        (1 + η a) * (∏ i ∈ s, (1 + η i) - 1) + η a := by
      rw [Finset.prod_insert ha]; ring
    rw [key, Finset.inf_insert]
    refine le_trans ?_ (v.map_add _ _)
    rw [min_comm, v.map_mul]
    refine min_le_min ?_ le_rfl
    calc s.inf (fun i => v (η i)) = 0 + s.inf (fun i => v (η i)) := (zero_add _).symm
      _ ≤ v (1 + η a) + v (∏ i ∈ s, (1 + η i) - 1) := add_le_add ha0 ih

end General

/-- **Small primes, product estimate.** Let `p` be a prime, `Λ` a finite nonempty set and
`η_ι ∈ ℚ_p` with `v_p(η_ι) ≥ 1`. Then
`v_p(∏_{ι ∈ Λ} (1 + η_ι) - 1) ≥ min_{ι ∈ Λ} v_p(η_ι)`. -/
@[zeta5irr "lem_small_prodexp"]
theorem inf'_le_padicAddValuation_prod_one_add_sub_one {p : ℕ} [Fact p.Prime] {ι : Type*}
    (Λ : Finset ι) (hΛ : Λ.Nonempty) {η : ι → ℚ_[p]}
    (hη : ∀ i ∈ Λ, 1 ≤ Padic.addValuation (η i)) :
    Λ.inf' hΛ (fun i => Padic.addValuation (η i)) ≤
      Padic.addValuation (∏ i ∈ Λ, (1 + η i) - 1) := by
  rw [Finset.inf'_eq_inf]
  exact finset_inf_le_addValuation_prod_one_add_sub_one _ Λ
    fun i hi => le_trans (by exact_mod_cast zero_le_one) (hη i hi)

end Zeta5Irr
