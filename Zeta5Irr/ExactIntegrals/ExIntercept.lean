/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExSlope

/-!
# The intercepts of `R` on the partition of `[3, 20]`

Let `t₀ < t₁ < ⋯` be the increasing enumeration of the breakpoint set `𝓔` of `[3, 20]`, and let
`aᵢ` be the slope of the inner limiting function `R` on `[tᵢ, tᵢ₊₁]`. For `0 ≤ i < #𝓔 - 1` the
intercept is
`bᵢ = R((2 tᵢ + tᵢ₊₁) / 3) - aᵢ (2 tᵢ + tᵢ₊₁) / 3`,
the value at `0` of the line of slope `aᵢ` through the point of the graph of `R` over the first
trisection point of `[tᵢ, tᵢ₊₁]`. Since `R` is affine on the open interval `(tᵢ, tᵢ₊₁)`, which
contains both trisection points, `x ↦ aᵢ x + bᵢ` is that affine function.

## Main definitions

* `Zeta5Irr.trisectionIntercept`: the intercept of the line through the graph of `f` over the
  two trisection points of `[l, r]`.
* `Zeta5Irr.exIntercept`: the intercept `bᵢ`.

## Main results

* `Zeta5Irr.trisectionIntercept_eq_of_eqOn`: if `f x = a x + b` on `(l, r)` with `l < r`, then
  the trisection intercept of `f` on `[l, r]` is `b`.
* `Zeta5Irr.exIntercept_def`: the source's formula for `bᵢ`.
* `Zeta5Irr.exIntercept_eq_of_eqOn`: if `R x = a x + b` on `(tᵢ, tᵢ₊₁)`, then `bᵢ = b`.

## Implementation notes

* As for `Zeta5Irr.exSlope`, the enumeration `i ↦ tᵢ` of `𝓔` is `Finset.orderEmbOfFin` and the
  index is a natural number `i` with `i + 1 < #𝓔`.
* `R` is real-valued, so `bᵢ` is a real number; that it is rational follows from `R` being affine
  with rational coefficients on `(tᵢ, tᵢ₊₁)`, via `Zeta5Irr.exIntercept_eq_of_eqOn`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.2 (The partition of `[3, 20]`).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Set

/-- The intercept `f((2l + r) / 3) - s (2l + r) / 3` of the line of slope
`s = trisectionSlope f l r` through the point of the graph of `f` over the first trisection
point `(2l + r) / 3` of `[l, r]`. -/
noncomputable def trisectionIntercept (f : ℝ → ℝ) (l r : ℝ) : ℝ :=
  f ((2 * l + r) / 3) - trisectionSlope f l r * ((2 * l + r) / 3)

/-- If `f` agrees with the affine function `x ↦ a x + b` on `(l, r)` and `l < r`, then the
trisection intercept of `f` on `[l, r]` is `b`. -/
theorem trisectionIntercept_eq_of_eqOn {f : ℝ → ℝ} {l r a b : ℝ} (hlr : l < r)
    (hf : EqOn f (fun x => a * x + b) (Ioo l r)) : trisectionIntercept f l r = b := by
  have h2 : (2 * l + r) / 3 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  rw [trisectionIntercept, trisectionSlope_eq_of_eqOn hlr hf, hf h2]
  ring

/-- The intercept `bᵢ = R((2 tᵢ + tᵢ₊₁) / 3) - aᵢ (2 tᵢ + tᵢ₊₁) / 3` of the inner limiting
function `R` on the `i`-th interval `[tᵢ, tᵢ₊₁]` of the partition of `[3, 20]`,
for `0 ≤ i < #𝓔 - 1`. -/
@[zeta5irr "def_ex_intercept"]
noncomputable def exIntercept {i : ℕ} (hi : i + 1 < #exBreaks) : ℝ :=
  trisectionIntercept innerLimitingR (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩)
    (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩)

/-- The source's formula for `bᵢ`. -/
theorem exIntercept_def {i : ℕ} (hi : i + 1 < #exBreaks) :
    exIntercept hi =
      innerLimitingR ((2 * (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) +
          (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) / 3) -
        exSlope hi * ((2 * (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) +
          (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) / 3) :=
  rfl

/-- If `R` agrees with `x ↦ a x + b` on `(tᵢ, tᵢ₊₁)`, then `bᵢ = b`. -/
theorem exIntercept_eq_of_eqOn {i : ℕ} (hi : i + 1 < #exBreaks) {a b : ℝ}
    (hR : EqOn innerLimitingR (fun x => a * x + b)
      (Ioo (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ)
        (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ))) :
    exIntercept hi = b :=
  trisectionIntercept_eq_of_eqOn (Rat.cast_lt.2 (orderEmbOfFin_exBreaks_lt_succ hi)) hR

end Zeta5Irr
