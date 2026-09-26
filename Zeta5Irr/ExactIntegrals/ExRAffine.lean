/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExIntercept
public import Zeta5Irr.ExactIntegrals.ExGammaAffine
public import Zeta5Irr.ExactIntegrals.ExNcalAffine

/-!
# The inner limiting function is affine between consecutive breakpoints

Let `t₀ < t₁ < ⋯` be the increasing enumeration of the breakpoint set `𝓔` of `[3, 20]`, and
let `aᵢ` and `bᵢ` be the trisection slope and intercept of the inner limiting function
`R = -Γ - 𝒩` on `[tᵢ, tᵢ₊₁]`. Since `Γ` and `𝒩` are both affine on `(tᵢ, tᵢ₊₁)`, so is `R`,
say `R(x) = a x + b` there. Evaluating at the two trisection points of `[tᵢ, tᵢ₊₁]`, which lie
in `(tᵢ, tᵢ₊₁)`, recovers `a = aᵢ` and `b = bᵢ`, so `R(x) = aᵢ x + bᵢ` on `(tᵢ, tᵢ₊₁)`.

## Main results

* `Zeta5Irr.innerLimitingR_eq_exSlope_mul_add_exIntercept`: for `i + 1 < #𝓔` and
  `tᵢ < x < tᵢ₊₁`, `R(x) = aᵢ x + bᵢ`.

## Implementation notes

* The increasing enumeration `i ↦ tᵢ` of `𝓔` is `Finset.orderEmbOfFin`, and the index is a
  natural number `i` with `i + 1 < #𝓔`, as in the source's `0 ≤ i < #𝓔 - 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.3 (The inner integral).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Set

/-- Let `t₀ < t₁ < ⋯` enumerate the breakpoint set `𝓔`. For every `i` with `i + 1 < #𝓔` and
every `x` with `tᵢ < x < tᵢ₊₁`, the inner limiting function satisfies `R(x) = aᵢ x + bᵢ`. -/
@[zeta5irr "lem_ex_R_affine"]
theorem innerLimitingR_eq_exSlope_mul_add_exIntercept {i : ℕ} (hi : i + 1 < #exBreaks)
    {x : ℝ} (hlx : (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) < x)
    (hxr : x < (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) :
    innerLimitingR x = exSlope hi * x + exIntercept hi := by
  obtain ⟨a₁, b₁, hΓ⟩ := exists_rat_innerLimitingGamma_eq_of_mem_Ioo_exBreaks hi
  obtain ⟨a₂, b₂, hN⟩ := exists_rat_scalarLimitingFunction_eq_of_mem_Ioo_exBreaks hi
  have hR : EqOn innerLimitingR (fun y => (-a₁ - a₂ : ℝ) * y + (-b₁ - b₂))
      (Ioo (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ)
        (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) := fun y hy => by
    rw [innerLimitingR_def, hΓ y hy.1 hy.2, hN y hy.1 hy.2]
    ring
  rw [exSlope_eq_of_eqOn hi hR, exIntercept_eq_of_eqOn hi hR]
  exact hR ⟨hlx, hxr⟩

end Zeta5Irr
