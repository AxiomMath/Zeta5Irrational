/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormPper
public import Zeta5Irr.PrimeSum.NormPhi

/-!
# The derivative of the first periodic antiderivative

Away from the jump set `ℤ ∪ α⁻¹ℤ`, the first periodic antiderivative
`𝒫(x) = 74 {α x} (1 - {α x}) - λ {x} (1 - {x})` is differentiable, with
`𝒫'(x) = Φ(x) + λ`, where `Φ(x) = 4λ + 2λ{x} - 12λ{αx}` is the sawtooth slope.

Near a point `t ∉ ℤ` the fractional part agrees with `s ↦ s - ⌊t⌋`, so it has derivative `1`
there. The chain rule gives `(t ↦ {t}(1 - {t}))' = 1 - 2{t}` at such points, and then
`𝒫'(x) = 74 α (1 - 2{αx}) - λ (1 - 2{x}) = 5λ + 2λ{x} - 12λ{αx}`, using `74 α - λ = 5λ` and
`148 α = 12λ` for `α = 3/40`, `λ = 37/40`.

## Main results

* `Zeta5Irr.hasDerivAt_fract_mul_one_sub_fract`: `t ↦ {t}(1 - {t})` has derivative
  `1 - 2{t}` at every non-integer `t`.
* `Zeta5Irr.hasDerivAt_firstPeriodicAntideriv`: `𝒫'(x) = Φ(x) + λ` for `x ∉ ℤ ∪ α⁻¹ℤ`.

## Implementation notes

* The condition `x ∉ α⁻¹ℤ` is stated as `α x ∉ ℤ`, which is equivalent since `α ≠ 0`, and is
  the form in which it is used.
* Differentiability of `𝒫` at `x` is the `HasDerivAt` statement itself; the corollary
  `Zeta5Irr.deriv_firstPeriodicAntideriv` records the value of `deriv`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9: the tail integral.
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology

/-- The function `t ↦ {t}(1 - {t})` has derivative `1 - 2{t}` at every non-integer `t`. -/
theorem hasDerivAt_fract_mul_one_sub_fract {t : ℝ} (ht : t ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt (fun s : ℝ => Int.fract s * (1 - Int.fract s)) (1 - 2 * Int.fract t) t := by
  have h := hasDerivAt_fract ht
  convert h.mul (h.const_sub 1) using 1
  ring

/-- Away from `ℤ ∪ α⁻¹ℤ`, the first periodic antiderivative `𝒫` is differentiable with
derivative `𝒫'(x) = Φ(x) + λ`. The condition `x ∉ α⁻¹ℤ` is written `α x ∉ ℤ`. -/
@[zeta5irr "lem_norm_Pprime"]
theorem hasDerivAt_firstPeriodicAntideriv {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (hαx : (innerRatio : ℝ) * x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt firstPeriodicAntideriv (sawtoothSlope x + orderRatio) x := by
  have h1 := (hasDerivAt_fract_mul_one_sub_fract hαx).comp x
    ((hasDerivAt_id x).const_mul (innerRatio : ℝ))
  have h2 := hasDerivAt_fract_mul_one_sub_fract hx
  have h := (h1.const_mul 74).sub (h2.const_mul (orderRatio : ℝ))
  unfold firstPeriodicAntideriv
  convert h using 1
  · ext s; simp [Function.comp]; ring
  · simp only [sawtoothSlope, innerRatio, orderRatio]; push_cast; ring

/-- Away from `ℤ ∪ α⁻¹ℤ`, `deriv 𝒫 x = Φ(x) + λ`. -/
theorem deriv_firstPeriodicAntideriv {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (hαx : (innerRatio : ℝ) * x ∉ Set.range ((↑) : ℤ → ℝ)) :
    deriv firstPeriodicAntideriv x = sawtoothSlope x + orderRatio :=
  (hasDerivAt_firstPeriodicAntideriv hx hαx).deriv

end Zeta5Irr
