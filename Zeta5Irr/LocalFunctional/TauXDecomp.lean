/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.DerivProdEval
public import Zeta5Irr.LocalFunctional.TauX
public import Mathlib.Tactic.ENatToNat

/-!
# `τ_X` on a Lagrange-type decomposition

Let `R ⊆ ℤ` be finite, `P ∈ ℚ[x]` and `c_r ∈ ℚ` for `r ∈ R`. If
`A = P E_R + ∑_{r ∈ R} c_r ∏_{r' ∈ R \ {r}} (x - r')`, then
`τ_X(A; R) = τ(P) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - X)`.

The sum `∑_r c_r E_{R \ {r}}` has degree less than `#R = deg E_R`, so it is the remainder of
`A` on division by `E_R` and `P` is the quotient. Evaluating at `r₀ ∈ R` kills `P E_R` and
every summand with `r ≠ r₀`, leaving `A(r₀) = c_{r₀} ∏_{r' ≠ r₀} (r₀ - r') = c_{r₀} E_R'(r₀)`.

## Main results

* `Zeta5Irr.tauX_eq_of_eq_mul_add_sum`: the formula for `τ_X(A; R)` above.

## Implementation notes

The coefficients `c_r` are given as a function `c : ℤ → ℚ`; only its values on `R` enter.
The product `∏_{r' ∈ R \ {r}} (x - r')` is the pole polynomial `E_{R \ {r}}`, written
`intPoleProduct (R.erase r) ℚ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.1 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C derivative eval)

/-- Evaluating `τ_X` on a Lagrange-type decomposition
`A = P E_R + ∑_{r ∈ R} c_r E_{R \ {r}}`: then
`τ_X(A; R) = τ(P) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - X)`. -/
@[zeta5irr "lem_tauX_decomp"]
theorem tauX_eq_of_eq_mul_add_sum {R : Finset ℤ} {A P : ℚ[X]} (c : ℤ → ℚ)
    (hA : A = P * intPoleProduct R ℚ + ∑ r ∈ R, C (c r) * intPoleProduct (R.erase r) ℚ) :
    tauX R A = C (tau P) + ∑ r ∈ R, C (c r) * (C (harmonicFive (reflectIndex r)) - X) := by
  have hB : (∑ r ∈ R, C (c r) * intPoleProduct (R.erase r) ℚ).degree < R.card := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff ?_).2 ?_)
    · exact WithBot.bot_lt_coe _
    · intro r hr
      refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [degree_intPoleProduct, Finset.card_erase_of_mem hr]
      refine lt_of_le_of_lt (add_le_add_left Polynomial.degree_C_le _) ?_
      have h0 : 0 < R.card := Finset.card_pos.2 ⟨r, hr⟩
      rw [zero_add]
      exact_mod_cast Nat.sub_lt h0 one_pos
  rw [tauX_eq_of_eq_add hA hB]
  congr 1
  refine Finset.sum_congr rfl fun r₀ hr₀ ↦ ?_
  congr 2
  have hprod : ∏ r' ∈ R.erase r₀, ((r₀ : ℚ) - r') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r' hr' ↦ sub_ne_zero.2 <| by
      exact_mod_cast (Finset.ne_of_mem_erase hr').symm
  have hder : (derivative (intPoleProduct R ℚ)).eval (r₀ : ℚ) =
      ∏ r' ∈ R.erase r₀, ((r₀ : ℚ) - r') :=
    eval_derivative_prod_X_sub_C R (fun r : ℤ ↦ (r : ℚ)) hr₀
  have hev : A.eval (r₀ : ℚ) = c r₀ * ∏ r' ∈ R.erase r₀, ((r₀ : ℚ) - r') := by
    rw [hA, Polynomial.eval_add, Polynomial.eval_mul, eval_intPoleProduct_of_mem R ℚ hr₀,
      mul_zero, zero_add, Polynomial.eval_finsetSum, Finset.sum_eq_single r₀]
    · rw [Polynomial.eval_mul, Polynomial.eval_C, eval_intPoleProduct]
    · intro r hr hne
      rw [Polynomial.eval_mul,
        eval_intPoleProduct_of_mem _ ℚ (Finset.mem_erase.2 ⟨hne.symm, hr₀⟩), mul_zero]
    · exact fun h ↦ absurd hr₀ h
  rw [hev, hder, mul_div_cancel_right₀ _ hprod]

end Zeta5Irr
