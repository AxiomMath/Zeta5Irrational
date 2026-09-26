/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.DerivProdEval
public import Zeta5Irr.LocalFunctional.LocalDeltaBound

/-!
# `δ_R` is norm-nonincreasing when the poles are `p`-adically separated

Let `R ⊆ ℤ` be finite and suppose that `r - r'` is a `p`-adic unit for all distinct
`r, r' ∈ R`. Then the near-pole decomposition `δ_R : ℚ_p[z] → 𝓑_R` satisfies
`‖δ_R(U)‖ ≤ ‖U‖` for every `U ∈ ℚ_p[z]`.

Indeed `E_R'(r) = ∏_{r' ∈ R \ {r}} (r - r')` is a product of `p`-adic units, so
`|E_R'(r)|_p = 1` for every `r ∈ R`, and the constant `C_R` of the general bound
`‖δ_R(U)‖ ≤ C_R ‖U‖` equals `1`.

## Main results

* `Zeta5Irr.norm_eval_derivative_intPoleProduct_eq_one`: `|E_R'(r)|_p = 1` for `r ∈ R`.
* `Zeta5Irr.norm_deltaR_le_norm`: `‖δ_R(U)‖ ≤ ‖U‖`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime] {R : Finset ℤ}

/-- If `r - r'` is a `p`-adic unit for all distinct `r, r' ∈ R`, then `|E_R'(r)|_p = 1` for
every `r ∈ R`. -/
theorem norm_eval_derivative_intPoleProduct_eq_one
    (hR : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → IsUnit ((r - r' : ℤ) : ℤ_[p])) {r : ℤ} (hr : r ∈ R) :
    ‖(derivative (intPoleProduct R ℚ_[p])).eval (r : ℚ_[p])‖ = 1 := by
  rw [intPoleProduct, eval_derivative_prod_X_sub_C R (fun s : ℤ => (s : ℚ_[p])) hr, norm_prod]
  refine Finset.prod_eq_one fun r' hr' => ?_
  obtain ⟨hne, hr'⟩ := Finset.mem_erase.mp hr'
  have h := PadicInt.isUnit_iff.mp (hR r hr r' hr' hne.symm)
  rwa [PadicInt.norm_def, PadicInt.coe_intCast, Int.cast_sub] at h

/-- **`δ_R` is norm-nonincreasing for `p`-adically separated poles.** If `R ⊆ ℤ` is finite
and `r - r'` is a `p`-adic unit for all distinct `r, r' ∈ R`, then `‖δ_R(U)‖ ≤ ‖U‖` for every
`U ∈ ℚ_p[z]`, where `‖U‖` is the Gauss norm of `U` in `ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_BT_norm_one"]
theorem norm_deltaR_le_norm
    (hR : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → IsUnit ((r - r' : ℤ) : ℤ_[p])) (U : ℚ_[p][X]) :
    ‖deltaR R U‖ ≤ ‖tateAlgebra.ofPolynomial p U‖ := by
  have hC : (⨆ r : R, ‖(derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])‖⁻¹) ≤ 1 :=
    Real.iSup_le (fun r => by
      rw [norm_eval_derivative_intPoleProduct_eq_one hR r.2, inv_one]) zero_le_one
  simpa [max_eq_left hC] using norm_deltaR_le (R := R) U

end Zeta5Irr
