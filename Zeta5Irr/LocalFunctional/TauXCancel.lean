/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauX

/-!
# Cancelling a common linear factor in `τ_X`

Let `R ⊆ ℤ` be finite, `r₀ ∈ R`, and let `A ∈ ℚ[x]` be divisible by `x - r₀`. Then
`τ_X(A; R) = τ_X(A / (x - r₀); R \ {r₀})`: the rational function `A / E_R` is unchanged by
cancelling the common factor `x - r₀` from numerator and denominator, and `τ_X` depends only on
that rational function. Concretely, writing `A = (x - r₀) A₁` and `R₁ = R \ {r₀}`, one has
`E_R = (x - r₀) E_{R₁}`; the residue of `A / E_R` at `r₀` vanishes, the residues at `r ∈ R₁` agree
after cancelling the nonzero factor `r - r₀`, and `A` and `A₁` have the same quotient by `E_R`
and `E_{R₁}` respectively.

## Main results

* `Zeta5Irr.tauX_X_sub_C_mul`: `τ_X((x - r₀) A₁; R) = τ_X(A₁; R \ {r₀})` for `r₀ ∈ R`.
* `Zeta5Irr.tauX_eq_tauX_divByMonic`: `τ_X(A; R) = τ_X(A / (x - r₀); R \ {r₀})` when `r₀ ∈ R`
  and `x - r₀ ∣ A`.

## Implementation notes

The quotient `A / (x - r₀)` is `A /ₘ (X - C r₀)`, the division by the monic polynomial
`x - r₀`, which is exact under the divisibility hypothesis. The set `R \ {r₀}` is written
`R.erase r₀`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.1 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C derivative eval)

/-- Cancelling a linear factor: for `r₀ ∈ R`, `τ_X((x - r₀) A₁; R) = τ_X(A₁; R \ {r₀})`. -/
theorem tauX_X_sub_C_mul {R : Finset ℤ} {r₀ : ℤ} (hr₀ : r₀ ∈ R) (A₁ : ℚ[X]) :
    tauX R ((X - C (r₀ : ℚ)) * A₁) = tauX (R.erase r₀) A₁ := by
  set R₁ := R.erase r₀
  set E₁ := intPoleProduct R₁ ℚ
  have hE : intPoleProduct R ℚ = (X - C (r₀ : ℚ)) * E₁ := by
    rw [← intPoleProduct_insert ℚ (Finset.notMem_erase r₀ R), Finset.insert_erase hr₀]
  have hcard : R.card = R₁.card + 1 := (Finset.card_erase_add_one hr₀).symm
  -- the polynomial parts agree
  have hA : (X - C (r₀ : ℚ)) * A₁ =
      (A₁ /ₘ E₁) * intPoleProduct R ℚ + (X - C (r₀ : ℚ)) * (A₁ %ₘ E₁) := by
    rw [hE]
    conv_lhs => rw [← Polynomial.modByMonic_add_div A₁ E₁]
    ring
  have hB : ((X - C (r₀ : ℚ)) * (A₁ %ₘ E₁)).degree < (R.card : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_X_sub_C, hcard]
    have h := Polynomial.degree_modByMonic_lt A₁ (monic_intPoleProduct R₁ ℚ)
    rw [degree_intPoleProduct] at h
    rw [Nat.cast_add, Nat.cast_one, add_comm (R₁.card : WithBot ℕ)]
    exact WithBot.add_lt_add_left WithBot.one_ne_bot h
  rw [tauX_eq_of_eq_add hA hB, tauX, ← Finset.add_sum_erase R _ hr₀]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_self, zero_mul, zero_div, map_zero, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hne : (r : ℚ) - r₀ ≠ 0 :=
    sub_ne_zero.2 (Int.cast_injective.ne (Finset.ne_of_mem_erase hr))
  have hd : (derivative (intPoleProduct R ℚ)).eval (r : ℚ) =
      ((r : ℚ) - r₀) * (derivative E₁).eval (r : ℚ) := by
    rw [hE, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
      eval_intPoleProduct_of_mem R₁ ℚ hr, zero_add, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [hd, mul_div_mul_left _ _ hne]

/-- **Cancellation of `x - r₀` in `τ_X`.** If `r₀ ∈ R` and `x - r₀` divides `A`, then
`τ_X(A; R) = τ_X(A / (x - r₀); R \ {r₀})`. -/
@[zeta5irr "lem_tauX_cancel"]
theorem tauX_eq_tauX_divByMonic {R : Finset ℤ} {r₀ : ℤ} (hr₀ : r₀ ∈ R) {A : ℚ[X]}
    (hA : X - C (r₀ : ℚ) ∣ A) :
    tauX R A = tauX (R.erase r₀) (A /ₘ (X - C (r₀ : ℚ))) := by
  conv_lhs => rw [← Polynomial.mul_divByMonic_eq_iff_isRoot.2
    (Polynomial.dvd_iff_isRoot.1 hA)]
  exact tauX_X_sub_C_mul hr₀ _

end Zeta5Irr
