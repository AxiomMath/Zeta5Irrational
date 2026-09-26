/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Gamma

/-!
# The two-variable inner functional `Γ̂(x, σ)`

For real `x` and `σ`, the source puts
`Γ̂(x, σ) = ∫₀^{1/2} (⌊2σ⌋ - b(x, z)) (⌊2σ⌋ + b(x, z) - ℓ(x, z) - 5) dz`
`  + ({2σ} / 2) (2 ⌊2σ⌋ - q̃(x) - 5) + ({2σ} / 2 - ñ(x))₊`,
where `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1` is the pole count, `b(x, z) = 3 ℓ(α x, z)` the
weighted pole count, `q̃(x) = ⌊2 x⌋` the pole count at the base and `ñ(x) = (2 x - q̃(x)) / 2`
its remainder. It is the inner limiting function `Γ` with the height `H x` replaced by a free
variable `σ`: `Γ̂(x, H x) = Γ(x)`.

## Main definitions

* `Zeta5Irr.innerLimitingGammaHat`: the functional `Γ̂(x, σ)`.

## Main results

* `Zeta5Irr.innerLimitingGammaHat_def`: the defining formula, with `(·)₊` as `max · 0`.
* `Zeta5Irr.innerLimitingGammaHat_heightRatio_mul`: `Γ̂(x, H x) = Γ(x)`.

## Implementation notes

* The source defines `Γ̂(x, σ)` for `x ≥ 3` and `σ > 0`. The formula makes sense for all real
  `x` and `σ`, so `Γ̂` is a total function of two real variables; the restrictions are carried
  by the lemmas that use them.
* The fractional part `{2σ}` is Mathlib's `Int.fract (2 * σ)` and the positive part is
  Mathlib's `posPart`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

/-- The two-variable inner functional
`Γ̂(x, σ) = ∫₀^{1/2} (⌊2σ⌋ - b(x, z)) (⌊2σ⌋ + b(x, z) - ℓ(x, z) - 5) dz`
`  + ({2σ} / 2) (2 ⌊2σ⌋ - q̃(x) - 5) + ({2σ} / 2 - ñ(x))₊`.
The source restricts to `x ≥ 3` and `σ > 0`; the formula is used for all real `x` and `σ`. -/
@[zeta5irr "def_norm_Gamhat"]
noncomputable def innerLimitingGammaHat (x σ : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), ((⌊2 * σ⌋ : ℝ) - weightedPoleCount x z) *
      ((⌊2 * σ⌋ : ℝ) + weightedPoleCount x z - ell x z - 5)) +
    Int.fract (2 * σ) / 2 * (2 * (⌊2 * σ⌋ : ℝ) - basePoleCount x - 5) +
    (Int.fract (2 * σ) / 2 - baseHalfFract x)⁺

/-- Unfolding lemma for `Γ̂`, with the positive part written as `max · 0`. -/
theorem innerLimitingGammaHat_def (x σ : ℝ) :
    innerLimitingGammaHat x σ =
      (∫ z in (0 : ℝ)..(1 / 2), ((⌊2 * σ⌋ : ℝ) - weightedPoleCount x z) *
          ((⌊2 * σ⌋ : ℝ) + weightedPoleCount x z - ell x z - 5)) +
        Int.fract (2 * σ) / 2 * (2 * (⌊2 * σ⌋ : ℝ) - basePoleCount x - 5) +
        max (Int.fract (2 * σ) / 2 - baseHalfFract x) 0 :=
  rfl

/-- At the height `σ = H x`, where `H` is the height ratio, `Γ̂` is the inner limiting
function: `Γ̂(x, H x) = Γ(x)`. -/
@[zeta5irr "lem_norm_Gamhat_Gamma"]
theorem innerLimitingGammaHat_heightRatio_mul (x : ℝ) :
    innerLimitingGammaHat x ((heightRatio : ℝ) * x) = innerLimitingGamma x := by
  have h : 2 * ((heightRatio : ℝ) * x) = 2 * (heightRatio : ℝ) * x := (mul_assoc _ _ _).symm
  rw [innerLimitingGammaHat, innerLimitingGamma, allocationRemainder_eq_half_fract, h,
    ← innerLimit_def]

end Zeta5Irr
