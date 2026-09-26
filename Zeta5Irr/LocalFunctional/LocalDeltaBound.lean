/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDelta
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The near-pole decomposition `δ_R` is bounded

Let `R ⊆ ℤ` be finite, `E_R = ∏_{r ∈ R} (z - r)` and
`C_R = max (1, max_{r ∈ R} |E_R'(r)|_p⁻¹)`. The near-pole decomposition
`δ_R : ℚ_p[z] → 𝓑_R` satisfies `‖δ_R(U)‖ ≤ C_R ‖U‖`, where `‖U‖` is the Gauss norm.

Both sides are homogeneous of degree one in `U`, so it suffices to treat `U` with `‖U‖ ≤ 1`,
i.e. `U ∈ ℤ_p[z]`. Since `E_R` is monic with integer coefficients, Euclidean division of such
`U` by `E_R` takes place in `ℤ_p[z]`, so the quotient has Gauss norm at most `1`; and each
residue `U(r) / E_R'(r)` has absolute value at most `|E_R'(r)|_p⁻¹` because `U(r) ∈ ℤ_p`.

## Main results

* `Zeta5Irr.norm_deltaR_le_of_norm_le_one`: `‖δ_R(U)‖ ≤ C_R` when `‖U‖ ≤ 1`.
* `Zeta5Irr.norm_deltaR_le`: `‖δ_R(U)‖ ≤ C_R ‖U‖` for every `U ∈ ℚ_p[z]`.

## Implementation notes

The Euclidean division in `ℤ_p[z]` is obtained from the one in `ℚ_p[z]` by
`Polynomial.map_divByMonic`, rather than by the source's induction on `deg U`. The bound on
the residues does not use that `E_R'(r) ≠ 0`: with the convention `0⁻¹ = 0` it holds
trivially otherwise.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime] {R : Finset ℤ}

/-- If every coefficient of `U ∈ ℚ_p[z]` has absolute value at most `1`, then `U` is the image
of a polynomial over `ℤ_p`. -/
private theorem exists_map_eq_of_norm_coeff_le_one {U : ℚ_[p][X]}
    (hU : ∀ d, ‖U.coeff d‖ ≤ 1) : ∃ V : ℤ_[p][X], V.map PadicInt.Coe.ringHom = U := by
  have : U ∈ lifts (PadicInt.Coe.ringHom (p := p)) :=
    (lifts_iff_coeff_lifts U).mpr fun d => ⟨⟨U.coeff d, hU d⟩, rfl⟩
  exact (mem_lifts U).mp this

/-- The norm of a polynomial in `ℚ_p⟨z⟩` bounds the absolute value of each coefficient. -/
private theorem norm_coeff_le_norm_ofPolynomial (U : ℚ_[p][X]) (d : ℕ) :
    ‖U.coeff d‖ ≤ ‖tateAlgebra.ofPolynomial p U‖ := by
  rw [tateAlgebra.norm_def, tateAlgebra.coe_ofPolynomial]
  simpa using le_tateNorm (coe_mem_tateAlgebra U) d

/-- A polynomial whose coefficients have absolute value at most `1` has norm at most `1` in
`ℚ_p⟨z⟩`. -/
private theorem norm_ofPolynomial_le_one {U : ℚ_[p][X]} (hU : ∀ d, ‖U.coeff d‖ ≤ 1) :
    ‖tateAlgebra.ofPolynomial p U‖ ≤ 1 := by
  rw [tateAlgebra.norm_def, tateAlgebra.coe_ofPolynomial]
  exact tateNorm_coe_le_of_forall_norm_coeff_le hU

/-- For `U ∈ ℚ_p[z]` of Gauss norm at most `1`, the near-pole decomposition satisfies
`‖δ_R(U)‖ ≤ C_R = max (1, max_{r ∈ R} |E_R'(r)|_p⁻¹)`. -/
theorem norm_deltaR_le_of_norm_le_one {U : ℚ_[p][X]}
    (hU : ‖tateAlgebra.ofPolynomial p U‖ ≤ 1) :
    ‖deltaR R U‖ ≤
      max 1 (⨆ r : R, ‖(derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹) := by
  obtain ⟨V, rfl⟩ := exists_map_eq_of_norm_coeff_le_one fun d =>
    (norm_coeff_le_norm_ofPolynomial U d).trans hU
  set f := PadicInt.Coe.ringHom (p := p)
  have hE : (intPoleProduct R ℤ_[p]).map f = intPoleProduct R ℚ_[p] := map_intPoleProduct _ _ _
  set C := ⨆ r : R, ‖(derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹
  have hC : 0 ≤ C := Real.iSup_nonneg fun _ => inv_nonneg.mpr (norm_nonneg _)
  rw [BT.norm_eq]
  refine max_le_max ?_ ?_
  · rw [deltaR_fst, ← hE, ← map_divByMonic f (monic_intPoleProduct R ℤ_[p])]
    refine norm_ofPolynomial_le_one fun d => ?_
    rw [coeff_map]
    exact PadicInt.norm_le_one _
  · refine Real.iSup_le (fun r => ?_) hC
    have hV : ‖V.eval₂ f ((r : ℤ) : ℚ_[p])‖ ≤ 1 := by
      rw [← map_intCast f, eval₂_at_apply]
      exact PadicInt.norm_le_one _
    rw [deltaR_res, norm_div, eval_map]
    refine (div_le_div_of_nonneg_right hV (norm_nonneg _)).trans ?_
    rw [one_div]
    exact le_ciSup (f := fun r : R =>
      ‖(derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹)
      (Finite.bddAbove_range _) r

/-- **The near-pole decomposition is bounded.** For a finite set `R ⊆ ℤ` and
`C_R = max (1, max_{r ∈ R} |E_R'(r)|_p⁻¹)`, every `U ∈ ℚ_p[z]` satisfies
`‖δ_R(U)‖ ≤ C_R ‖U‖`, where `‖U‖` is the Gauss norm of `U` in `ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_local_delta_bound"]
theorem norm_deltaR_le (U : ℚ_[p][X]) :
    ‖deltaR R U‖ ≤
      max 1 (⨆ r : R, ‖(derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹) *
        ‖tateAlgebra.ofPolynomial p U‖ := by
  set C := max 1 (⨆ r : R, ‖(derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹)
  rcases eq_or_ne U 0 with rfl | hU0
  · have : deltaR R (0 : ℚ_[p][X]) = 0 := by
      simpa using deltaR_smul (R := R) (0 : ℚ_[p]) 0
    simp [this]
  -- a coefficient `c` of `U` of maximal absolute value
  obtain ⟨d, hd, hmax⟩ := U.support.exists_max_image (fun d => ‖U.coeff d‖)
    (support_nonempty.mpr hU0)
  set c := U.coeff d
  have hc : c ≠ 0 := mem_support_iff.mp hd
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hbound : ∀ e, ‖(c⁻¹ • U).coeff e‖ ≤ 1 := fun e => by
    rw [coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]
    by_cases he : e ∈ U.support
    · exact hmax e he
    · rw [notMem_support_iff.mp he, norm_zero]; exact hcpos.le
  have key := norm_deltaR_le_of_norm_le_one (R := R) (norm_ofPolynomial_le_one hbound)
  rw [deltaR_smul, norm_smul, norm_inv, inv_mul_le_iff₀ hcpos] at key
  rw [mul_comm]
  exact key.trans (mul_le_mul_of_nonneg_right (norm_coeff_le_norm_ofPolynomial U d)
    (zero_le_one.trans (le_max_left _ _)))

end Zeta5Irr
