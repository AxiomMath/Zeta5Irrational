/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.LocalDeltaDiv
public import Zeta5Irr.LocalFunctional.TauFar
public import Zeta5Irr.LocalFunctional.DerivProdEval

/-!
# `δ_R^ext` of a partial-fraction decomposition

Let `R ⊆ ℤ` be finite and `Σ ⊆ ℚ_p` finite with `v_p(s) < 0` for `s ∈ Σ`, and write
`E_R = ∏_{r ∈ R} (z - r)` and `ε_s = 1 / (z - s) ∈ ℚ_p⟨z⟩`. If a polynomial `A ∈ ℚ_p[z]`
decomposes as
`A = P E_R ∏_{s ∈ Σ} (z - s) + ∑_{r ∈ R} c_r ∏_{r' ≠ r} (z - r') ∏_{s ∈ Σ} (z - s)
  + ∑_{s ∈ Σ} e_s E_R ∏_{s' ≠ s} (z - s')`,
which is to say `A / ∏_s (z - s) = P E_R + ∑_r c_r E_R / (z - r) + ∑_s e_s E_R / (z - s)`, then
`δ_R^ext(A ∏_s ε_s) = (P + ∑_s e_s ε_s, (c_r)_{r ∈ R})`.

Multiplying the identity by `∏_s ε_s` and using `(z - s) ε_s = 1` gives
`A ∏_s ε_s = (P + ∑_s e_s ε_s) E_R + b` with `b = ∑_r c_r ∏_{r' ≠ r} (z - r')` of degree `< #R`,
and `b(r) = c_r E_R'(r)` for `r ∈ R`; the claim follows from the computation of `δ_R^ext` of a
division by `E_R`.

## Main results

* `Zeta5Irr.deltaExt_mul_prod_farEps`: `δ_R^ext(A ∏_s ε_s) = (P + ∑_s e_s ε_s, (c_r)_{r ∈ R})`.

## Implementation notes

* The source assumes `R` nonempty; this is not needed.
* The Tate-algebra component `P + ∑_s e_s ε_s` of the result is passed as an element `q` of
  `ℚ_p⟨z⟩` together with the identity `q = P + ∑_s e_s ε_s` in `ℚ_p⟦z⟧`, which determines it.
* The coefficients `c_r` and `e_s` are given as functions on `ℤ` and on `ℚ_p`; only their values
  on `R` and on `Σ` enter. The product `∏_{r' ∈ R \ {r}} (z - r')` is `E_{R \ {r}}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset
open scoped PowerSeries

/-- `∏_{s ∈ T} (z - s) · ∏_{s ∈ T} ε_s = 1` when no `s ∈ T` is zero. -/
theorem coe_prod_X_sub_C_mul_prod_farEps {K : Type*} [Field K] {T : Finset K}
    (hT : ∀ s ∈ T, s ≠ 0) : ((∏ s ∈ T, (X - C s) : K[X]) : K⟦X⟧) * ∏ s ∈ T, farEps s = 1 := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, ← prod_mul_distrib]
  refine prod_eq_one fun s hs => ?_
  rw [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]
  exact X_sub_C_mul_farEps (hT s hs)

variable {p : ℕ} [Fact p.Prime]

/-- `∑_{r ∈ R} c_r E_{R \ {r}}` has degree `< #R`. -/
theorem degree_sum_C_mul_intPoleProduct_erase_lt (R : Finset ℤ) (c : ℤ → ℚ_[p]) :
    (∑ r ∈ R, C (c r) * intPoleProduct (R.erase r) ℚ_[p]).degree < R.card := by
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_)
  intro r hr
  refine (degree_mul_le _ _).trans_lt ?_
  refine (add_le_add degree_C_le (degree_intPoleProduct _ _).le).trans_lt ?_
  rw [zero_add, card_erase_of_mem hr, Nat.cast_lt]
  have := card_pos.mpr ⟨r, hr⟩
  omega

/-- For `r ∈ R`, `(∑_{r' ∈ R} c_{r'} E_{R \ {r'}})(r) / E_R'(r) = c_r`. -/
theorem eval_sum_C_mul_intPoleProduct_erase_div {R : Finset ℤ} (c : ℤ → ℚ_[p]) {r : ℤ}
    (hr : r ∈ R) :
    (∑ r' ∈ R, C (c r') * intPoleProduct (R.erase r') ℚ_[p]).eval (r : ℚ_[p]) /
      (derivative (intPoleProduct R ℚ_[p])).eval (r : ℚ_[p]) = c r := by
  have hbr : (∑ r' ∈ R, C (c r') * intPoleProduct (R.erase r') ℚ_[p]).eval (r : ℚ_[p]) =
      c r * ∏ r' ∈ R.erase r, ((r : ℚ_[p]) - (r' : ℚ_[p])) := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_intPoleProduct]
    rw [sum_eq_single r]
    · intro r' _ hr'
      exact mul_eq_zero_of_right _ (prod_eq_zero (mem_erase.mpr ⟨Ne.symm hr', hr⟩) (sub_self _))
    · exact fun h => absurd hr h
  have hne : ∏ r' ∈ R.erase r, ((r : ℚ_[p]) - (r' : ℚ_[p])) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun r' hr' => sub_ne_zero.mpr ?_
    exact_mod_cast (Ne.symm (ne_of_mem_erase hr'))
  have hder : (derivative (intPoleProduct R ℚ_[p])).eval (r : ℚ_[p]) =
      ∏ r' ∈ R.erase r, ((r : ℚ_[p]) - (r' : ℚ_[p])) :=
    eval_derivative_prod_X_sub_C R (fun r : ℤ => (r : ℚ_[p])) hr
  rw [hbr, hder, mul_div_cancel_right₀ _ hne]

open Classical in
/-- **Compatibility of `δ_R^ext` with partial fractions.** Let `R ⊆ ℤ` be finite, `Σ ⊆ ℚ_p`
finite with `v_p(s) < 0` for `s ∈ Σ`, and let `A, P ∈ ℚ_p[z]`, `c_r, e_s ∈ ℚ_p` satisfy
`A = P E_R ∏_{s ∈ Σ} (z - s) + ∑_{r ∈ R} c_r E_{R \ {r}} ∏_{s ∈ Σ} (z - s)
  + ∑_{s ∈ Σ} e_s E_R ∏_{s' ∈ Σ \ {s}} (z - s')`.
Then `δ_R^ext(A ∏_{s ∈ Σ} ε_s) = (P + ∑_{s ∈ Σ} e_s ε_s, (c_r)_{r ∈ R})`. -/
@[zeta5irr "lem_local_compat"]
theorem deltaExt_mul_prod_farEps {R : Finset ℤ} {S : Finset ℚ_[p]}
    (hS : ∀ s ∈ S, s.valuation < 0) {A P : ℚ_[p][X]} {c : ℤ → ℚ_[p]} {e : ℚ_[p] → ℚ_[p]}
    (hA : A = P * intPoleProduct R ℚ_[p] * ∏ s ∈ S, (X - C s)
      + ∑ r ∈ R, C (c r) * intPoleProduct (R.erase r) ℚ_[p] * ∏ s ∈ S, (X - C s)
      + ∑ s ∈ S, C (e s) * intPoleProduct R ℚ_[p] * ∏ s' ∈ S.erase s, (X - C s'))
    {q : tateAlgebra p}
    (hq : (q : ℚ_[p]⟦X⟧) = (P : ℚ_[p]⟦X⟧) + ∑ s ∈ S, PowerSeries.C (e s) * farEps s) :
    deltaExt R ((A : ℚ_[p]⟦X⟧) * ∏ s ∈ S, farEps s) = BT.mk q fun r => c r := by
  set b : ℚ_[p][X] := ∑ r ∈ R, C (c r) * intPoleProduct (R.erase r) ℚ_[p]
  let φ := Polynomial.coeToPowerSeries.ringHom (R := ℚ_[p])
  have hφ : ∀ U : ℚ_[p][X], φ U = (U : ℚ_[p]⟦X⟧) := fun _ => rfl
  have hne : ∀ s ∈ S, s ≠ 0 := fun s hs h0 => by simpa [h0] using hS s hs
  have hmulE : (A : ℚ_[p]⟦X⟧) * ∏ s ∈ S, farEps s =
      (q : ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + b := by
    rw [hA, hq]
    simp only [← hφ, map_add, map_mul, map_sum]
    simp only [hφ, Polynomial.coe_C]
    have h1 := coe_prod_X_sub_C_mul_prod_farEps hne
    have h2 : ∀ s ∈ S, ((∏ s' ∈ S.erase s, (X - C s') : ℚ_[p][X]) : ℚ_[p]⟦X⟧) *
        ∏ s ∈ S, farEps s = farEps s := by
      intro s hs
      rw [← mul_prod_erase S _ hs, mul_left_comm,
        coe_prod_X_sub_C_mul_prod_farEps fun s' hs' => hne s' (mem_of_mem_erase hs'), mul_one]
    have ht1 : (P : ℚ_[p]⟦X⟧) * intPoleProduct R ℚ_[p] *
        ((∏ s ∈ S, (X - C s) : ℚ_[p][X]) : ℚ_[p]⟦X⟧) * ∏ s ∈ S, farEps s =
        (P : ℚ_[p]⟦X⟧) * intPoleProduct R ℚ_[p] := by
      rw [mul_assoc, h1, mul_one]
    have ht2 : ∀ r ∈ R, PowerSeries.C (c r) * (intPoleProduct (R.erase r) ℚ_[p] : ℚ_[p]⟦X⟧) *
        ((∏ s ∈ S, (X - C s) : ℚ_[p][X]) : ℚ_[p]⟦X⟧) * ∏ s ∈ S, farEps s =
        PowerSeries.C (c r) * (intPoleProduct (R.erase r) ℚ_[p] : ℚ_[p]⟦X⟧) := by
      intro r _
      rw [mul_assoc, h1, mul_one]
    have ht3 : ∀ s ∈ S, PowerSeries.C (e s) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) *
        ((∏ s' ∈ S.erase s, (X - C s') : ℚ_[p][X]) : ℚ_[p]⟦X⟧) * ∏ s ∈ S, farEps s =
        PowerSeries.C (e s) * farEps s * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) := by
      intro s hs
      rw [mul_assoc, h2 s hs, mul_right_comm]
    have hbc : (b : ℚ_[p]⟦X⟧) =
        ∑ r ∈ R, PowerSeries.C (c r) * (intPoleProduct (R.erase r) ℚ_[p] : ℚ_[p]⟦X⟧) := by
      rw [← hφ, map_sum]
      simp only [hφ, Polynomial.coe_mul, Polynomial.coe_C]
    rw [add_mul, add_mul, sum_mul, sum_mul, ht1, sum_congr rfl ht2, sum_congr rfl ht3, hbc,
      add_mul, sum_mul]
    ring
  rw [deltaExt_eq_of_eq_mul_add (degree_sum_C_mul_intPoleProduct_erase_lt R c) hmulE]
  congr 1
  funext r
  exact eval_sum_C_mul_intPoleProduct_erase_div c r.2

end Zeta5Irr
