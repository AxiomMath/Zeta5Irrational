/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.R
public import Zeta5Irr.PrimeSum.NormPhi
public import Zeta5Irr.PrimeSum.NormEcal
public import Zeta5Irr.PrimeSum.NormDeltaFormula
public import Zeta5Irr.PrimeSum.NormUppersetMeasure
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat

/-!
# The splitting of the inner limiting function

With `α = 3/40` and `λ = 37/40`, the inner limiting function `R = -Γ - 𝒩` splits as
`R(x) = x Φ(x) + 𝓔(x)`, where `Φ(x) = 4λ + 2λ{x} - 12λ{αx}` is the sawtooth slope and
`𝓔(x)` is the error term collecting the bounded contributions.

The proof expands `𝒩` and `Γ` after writing every floor as the argument minus its fractional
part, and writing `ℓ(x, z) = 2x + δ(x, z)`. The terms of `Γ` linear in `δ` integrate to `0`,
because `∫_0^{1/2} δ(x, z) dz = |S(x)| - {2x}/2 = 0`. The coefficients of `x²` then cancel
and the terms linear in `x` assemble to `x Φ(x)`.

## Main results

* `Zeta5Irr.innerLimitingR_eq_mul_sawtoothSlope_add`: `R(x) = x Φ(x) + 𝓔(x)`, with `𝓔(x)`
  written out as its defining formula.

## Implementation notes

* The source states the splitting for `x ≥ 3`. The functions involved are defined on all of
  `ℝ` and the identity holds for every real `x`, so the hypothesis is dropped.
* The error term is written out explicitly on the right-hand side, as
  `(2s̃(2s̃ - 2ñ) - (2s̃ - 2ñ)₊ + {2λx}(1 - {2λx})) / 2 + 9 ∫ δ(αx, z)² dz
  - 3 ∫ δ(x, z) δ(αx, z) dz`, with the two integrals over `[0, 1/2]` kept separate.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.5 (The splitting of the inner limiting function).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- **Splitting of the inner limiting function**, with the error term written out:
with `α = 3/40` and `λ = 37/40`,
`R(x) = x Φ(x) + (2s̃(2s̃ - 2ñ) - (2s̃ - 2ñ)₊ + {2λx}(1 - {2λx})) / 2
  + 9 ∫_0^{1/2} δ(αx, z)² dz - 3 ∫_0^{1/2} δ(x, z) δ(αx, z) dz`. -/
theorem innerLimitingR_eq_mul_sawtoothSlope_add (x : ℝ) :
    innerLimitingR x = x * sawtoothSlope x +
      ((2 * allocationRemainder x * (2 * allocationRemainder x - 2 * baseHalfFract x) -
          (2 * allocationRemainder x - 2 * baseHalfFract x)⁺ +
          Int.fract (2 * (orderRatio : ℝ) * x) *
            (1 - Int.fract (2 * (orderRatio : ℝ) * x))) / 2 +
        9 * (∫ z in (0 : ℝ)..(1 / 2), ellDeviation ((innerRatio : ℝ) * x) z ^ 2) -
        3 * ∫ z in (0 : ℝ)..(1 / 2),
          ellDeviation x z * ellDeviation ((innerRatio : ℝ) * x) z) := by
  have hT : innerLimit x = 2 * heightRatio * x - 2 * allocationRemainder x := by
    rw [allocationRemainder_def]; ring
  have hq : basePoleCount x = 2 * x - 2 * baseHalfFract x := by
    rw [baseHalfFract_def]; ring
  have hp : (2 * allocationRemainder x - 2 * baseHalfFract x)⁺ =
      2 * (allocationRemainder x - baseHalfFract x)⁺ := by
    rw [show 2 * allocationRemainder x - 2 * baseHalfFract x =
      2 * (allocationRemainder x - baseHalfFract x) by ring]
    simp only [posPart_def]
    rcases le_total (allocationRemainder x - baseHalfFract x) 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
  have h2 : (2 * (orderRatio : ℝ) * x) = 2 * ((orderRatio : ℝ) * x) := by ring
  have hf₁ : (⌊x⌋ : ℝ) = x - Int.fract x := (Int.self_sub_fract x).symm
  have hf₂ : (⌊(innerRatio : ℝ) * x⌋ : ℝ) =
      innerRatio * x - Int.fract ((innerRatio : ℝ) * x) :=
    (Int.self_sub_fract _).symm
  have hf₃ : (⌊2 * ((orderRatio : ℝ) * x)⌋ : ℝ) =
      2 * ((orderRatio : ℝ) * x) - Int.fract (2 * ((orderRatio : ℝ) * x)) :=
    (Int.self_sub_fract _).symm
  rw [innerLimitingR_def, innerLimitingGamma_def, integral_innerIntegrand_eq, ← ellDeviation_eq_psi,
    scalarLimitingFunction_def, innerLimitingFunction, sawtoothSlope, h2,
    ← posPart_def, hp, hf₁, hf₂, hf₃, hq, hT]
  generalize (∫ z in (0 : ℝ)..(1 / 2), ellDeviation ((innerRatio : ℝ) * x) z ^ 2) = I₁
  generalize (∫ z in (0 : ℝ)..(1 / 2),
    ellDeviation x z * ellDeviation ((innerRatio : ℝ) * x) z) = I₂
  generalize Int.fract x = φ
  generalize Int.fract ((innerRatio : ℝ) * x) = β
  generalize Int.fract (2 * ((orderRatio : ℝ) * x)) = υ
  norm_num [heightRatio, innerRatio, orderRatio]
  ring

/-- **Splitting of the inner limiting function**: `R(x) = x Φ(x) + 𝓔(x)`. -/
@[zeta5irr "lem_QR_split"]
theorem innerLimitingR_eq (x : ℝ) :
    innerLimitingR x = x * sawtoothSlope x + innerSplitError x := by
  rw [innerSplitError_def]; exact innerLimitingR_eq_mul_sawtoothSlope_add x

end Zeta5Irr
