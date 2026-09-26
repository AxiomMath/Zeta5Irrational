/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauFar
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.Polynomial.Basic

/-!
# Unit expansion of products of linear factors and far-pole series

Let `p` be a prime, `Λ`, `Λ'` finite sets, `w_η ∈ ℤ_p^×` for `η ∈ Λ` and `m_η' ∈ ℤ_p^×` for
`η' ∈ Λ'`. Then
`∏_{η ∈ Λ} (w_η + p z) · ∏_{η' ∈ Λ'} p⁻¹ ε_{m_η'/p} = ∑_{k ≥ 0} p^k γ_k z^k`
in `ℚ_p[[z]]`, with `γ_k ∈ ℤ_p` and `γ_0 ∈ ℤ_p^×`.

The proof exhibits the product as the image of a power series over `ℤ_p` under the ring
homomorphism `ℤ_p[[z]] → ℚ_p[[z]]`, `f(z) ↦ f(pz)`: the factor `w_η + pz` is the image of
`w_η + z`, and `p⁻¹ ε_{m/p}` is the image of `-∑_k m^{-k-1} z^k`. The constant coefficient of
the product over `ℤ_p` is a product of units.

## Main results

* `Zeta5Irr.exists_unit_expansion`: the expansion, with `γ_0` a unit of `ℤ_p`.

## Implementation notes

* The finite sets `Λ`, `Λ'` are `Finset`s of arbitrary index types.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

private lemma coe_units_inv (m : ℤ_[p]ˣ) :
    (((m⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = ((m : ℤ_[p]) : ℚ_[p])⁻¹ := by
  have h : (((m⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((m : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
  exact eq_inv_of_mul_eq_one_left h

variable (p) in
/-- The ring homomorphism `ℤ_p⟦z⟧ → ℚ_p⟦z⟧`, `h(z) ↦ h(pz)`. -/
noncomputable def padicIntRescale : ℤ_[p]⟦X⟧ →+* ℚ_[p]⟦X⟧ :=
  (rescale (p : ℚ_[p])).comp (map PadicInt.Coe.ringHom)

/-- The coefficients of `h(pz)` are `p^k h_k`. -/
theorem coeff_padicIntRescale (h : ℤ_[p]⟦X⟧) (k : ℕ) :
    coeff k (padicIntRescale p h) = (p : ℚ_[p]) ^ k * ((coeff k h : ℤ_[p]) : ℚ_[p]) := by
  rw [padicIntRescale, RingHom.comp_apply, coeff_rescale, coeff_map]
  rfl

/-- **Unit expansion.** For units `w_η, m_η'` of `ℤ_p`, the power series
`∏_η (w_η + p z) · ∏_η' p⁻¹ ε_{m_η'/p}` equals `∑_k p^k γ_k z^k` with `γ_k ∈ ℤ_p` and `γ_0` a
unit of `ℤ_p`. -/
@[zeta5irr "lem_in_unit_expansion"]
theorem exists_unit_expansion {ι ι' : Type*} (Λ : Finset ι) (Λ' : Finset ι')
    (w : ι → ℤ_[p]ˣ) (m : ι' → ℤ_[p]ˣ) :
    ∃ γ : ℕ → ℤ_[p], IsUnit (γ 0) ∧
      (∏ η ∈ Λ, (C ((w η : ℤ_[p]) : ℚ_[p]) + C (p : ℚ_[p]) * X)) *
        ∏ η' ∈ Λ', (C (p : ℚ_[p])⁻¹ * farEps (((m η' : ℤ_[p]) : ℚ_[p]) / p)) =
      PowerSeries.mk fun k => (p : ℚ_[p]) ^ k * (γ k : ℚ_[p]) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  set F : ℤ_[p]⟦X⟧ := (∏ η ∈ Λ, (C (w η : ℤ_[p]) + X)) *
    ∏ η' ∈ Λ', PowerSeries.mk fun k => -(((m η')⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ (k + 1) with hF
  refine ⟨fun k => coeff k F, ?_, ?_⟩
  · simp only [coeff_zero_eq_constantCoeff_apply, hF, map_mul, map_prod, map_add,
      constantCoeff_C, constantCoeff_X, add_zero, ← coeff_zero_eq_constantCoeff (R := ℤ_[p]),
      coeff_mk, zero_add, pow_one]
    refine IsUnit.mul (IsUnit.prod_iff.mpr fun η _ => (w η).isUnit)
      (IsUnit.prod_iff.mpr fun η' _ => ((m η')⁻¹).isUnit.neg)
  · trans padicIntRescale p F
    · rw [hF, map_mul, map_prod, map_prod]
      congr 1
      · refine Finset.prod_congr rfl fun η _ => ?_
        ext k
        rw [coeff_padicIntRescale]
        rcases k with _ | _ | k <;> simp [coeff_X, -map_natCast]
      · refine Finset.prod_congr rfl fun η' _ => ?_
        ext k
        rw [coeff_padicIntRescale, coeff_mk, coeff_C_mul, coeff_farEps]
        push_cast
        rw [coe_units_inv]
        field_simp
        ring
    · ext k
      rw [coeff_padicIntRescale, coeff_mk]

end Zeta5Irr
