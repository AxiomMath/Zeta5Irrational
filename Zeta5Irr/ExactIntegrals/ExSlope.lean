/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.R
public import Zeta5Irr.ExactIntegrals.ExBreaks

/-!
# The slopes of `R` on the partition of `[3, 20]`

Let `t₀ < t₁ < ⋯` be the increasing enumeration of the breakpoint set `𝓔` of `[3, 20]`.
For `0 ≤ i < #𝓔 - 1` the slope `aᵢ` is the difference quotient of the inner limiting function
`R` between the two trisection points of `[tᵢ, tᵢ₊₁]`:
`aᵢ = 3 / (tᵢ₊₁ - tᵢ) * (R((tᵢ + 2 tᵢ₊₁) / 3) - R((2 tᵢ + tᵢ₊₁) / 3))`.
Since `R` is affine on each open interval `(tᵢ, tᵢ₊₁)`, which contains both trisection points,
`aᵢ` is the slope of that affine function.

## Main definitions

* `Zeta5Irr.trisectionSlope`: the difference quotient of `f` between the trisection points of
  `[l, r]`.
* `Zeta5Irr.exSlope`: the slope `aᵢ`.

## Main results

* `Zeta5Irr.trisectionSlope_eq_of_eqOn`: if `f x = a x + b` on `(l, r)` with `l < r`, then the
  trisection slope of `f` on `[l, r]` is `a`.
* `Zeta5Irr.exSlope_def`: the source's formula for `aᵢ`.
* `Zeta5Irr.exSlope_eq_of_eqOn`: if `R x = a x + b` on `(tᵢ, tᵢ₊₁)`, then `aᵢ = a`.

## Implementation notes

* The increasing enumeration `i ↦ tᵢ` of `𝓔` is `Finset.orderEmbOfFin`, and the index is a
  natural number `i` with `i + 1 < #𝓔`, as in the source's `0 ≤ i < #𝓔 - 1`.
* `R` is real-valued, so `aᵢ` is a real number; that it is rational follows from `R` being
  affine with rational coefficients on `(tᵢ, tᵢ₊₁)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.2 (The partition of `[3, 20]`).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Set

/-- The difference quotient `3 / (r - l) * (f((l + 2r) / 3) - f((2l + r) / 3))` of `f` between
the two trisection points of `[l, r]`. -/
noncomputable def trisectionSlope (f : ℝ → ℝ) (l r : ℝ) : ℝ :=
  3 / (r - l) * (f ((l + 2 * r) / 3) - f ((2 * l + r) / 3))

/-- If `f` agrees with the affine function `x ↦ a x + b` on `(l, r)` and `l < r`, then the
trisection slope of `f` on `[l, r]` is `a`. -/
theorem trisectionSlope_eq_of_eqOn {f : ℝ → ℝ} {l r a b : ℝ} (hlr : l < r)
    (hf : EqOn f (fun x => a * x + b) (Ioo l r)) : trisectionSlope f l r = a := by
  have h1 : (l + 2 * r) / 3 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have h2 : (2 * l + r) / 3 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have hne : r - l ≠ 0 := by linarith
  rw [trisectionSlope, hf h1, hf h2]
  field_simp
  ring

/-- Consecutive breakpoints of `𝓔` are strictly increasing: `tᵢ < tᵢ₊₁`. -/
theorem orderEmbOfFin_exBreaks_lt_succ {i : ℕ} (hi : i + 1 < #exBreaks) :
    exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ < exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ := by
  simp only [OrderEmbedding.lt_iff_lt, Fin.mk_lt_mk]
  omega

/-- The slope `aᵢ = 3 / (tᵢ₊₁ - tᵢ) * (R((tᵢ + 2 tᵢ₊₁) / 3) - R((2 tᵢ + tᵢ₊₁) / 3))` of the
inner limiting function `R` on the `i`-th interval `[tᵢ, tᵢ₊₁]` of the partition of `[3, 20]`,
for `0 ≤ i < #𝓔 - 1`. -/
@[zeta5irr "def_ex_slope"]
noncomputable def exSlope {i : ℕ} (hi : i + 1 < #exBreaks) : ℝ :=
  trisectionSlope innerLimitingR (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩)
    (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩)

/-- The source's formula for `aᵢ`. -/
theorem exSlope_def {i : ℕ} (hi : i + 1 < #exBreaks) :
    exSlope hi =
      3 / ((exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ) -
          (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ)) *
        (innerLimitingR (((exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) +
            2 * (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) / 3) -
          innerLimitingR ((2 * (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) +
            (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) / 3)) :=
  rfl

/-- If `R` agrees with `x ↦ a x + b` on `(tᵢ, tᵢ₊₁)`, then `aᵢ = a`. -/
theorem exSlope_eq_of_eqOn {i : ℕ} (hi : i + 1 < #exBreaks) {a b : ℝ}
    (hR : EqOn innerLimitingR (fun x => a * x + b)
      (Ioo (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ)
        (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ))) :
    exSlope hi = a :=
  trisectionSlope_eq_of_eqOn (Rat.cast_lt.2 (orderEmbOfFin_exBreaks_lt_succ hi)) hR

end Zeta5Irr
