/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.PrimeSum.NormG0

/-!
# The second periodic antiderivative `𝒫₂`

For `x ∈ ℝ` the second periodic antiderivative is
`𝒫₂(x) = (74 / α) G₀({α x}) - λ G₀({x})`, where `G₀` is the cubic kernel, `{·}` is the
fractional part, and `α = 3/40`, `λ = 37/40` are the ratios of the construction. Off the
breakpoints `ℤ ∪ α⁻¹ ℤ` its derivative is the first periodic antiderivative `𝒫` minus the
constant `2923/240`, so it is used to integrate the tail of the prime sum by parts twice.
Since `α · 40 = 3` is an integer, `𝒫₂` is periodic of period `40`.

## Main definitions

* `Zeta5Irr.secondPeriodicAntideriv`: the function
  `x ↦ (74 / α) G₀({α x}) - λ G₀({x})` on `ℝ`.

## Main results

* `Zeta5Irr.secondPeriodicAntideriv_zero`: `𝒫₂(0) = 0`.
* `Zeta5Irr.secondPeriodicAntideriv_add_forty`: `𝒫₂(x + 40) = 𝒫₂(x)`.

## Implementation notes

* The source calls this function `𝒞`; the blueprint renames it `𝒫₂` to record that it is a
  second antiderivative of `𝒫`. It is kept in terms of `G₀` rather than expanded, so that
  statements about `G₀` apply to it directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9: the tail integral.
-/

@[expose] public section

namespace Zeta5Irr

/-- The second periodic antiderivative `𝒫₂(x) = (74 / α) G₀({α x}) - λ G₀({x})`, with
`α = 3/40` the inner ratio, `λ = 37/40` the order ratio and `G₀` the cubic kernel. The
source calls it `𝒞`. -/
@[zeta5irr "def_norm_P2"]
noncomputable def secondPeriodicAntideriv (x : ℝ) : ℝ :=
  74 / (innerRatio : ℝ) * cubicKernel (Int.fract ((innerRatio : ℝ) * x)) -
    (orderRatio : ℝ) * cubicKernel (Int.fract x)

/-- `𝒫₂(0) = 0`. -/
@[simp]
theorem secondPeriodicAntideriv_zero : secondPeriodicAntideriv 0 = 0 := by
  simp [secondPeriodicAntideriv]

/-- `𝒫₂` is periodic of period `40`, since `40` and `40 α = 3` are both integers. -/
theorem secondPeriodicAntideriv_add_forty (x : ℝ) :
    secondPeriodicAntideriv (x + 40) = secondPeriodicAntideriv x := by
  have h : (innerRatio : ℝ) * (x + 40) = (innerRatio : ℝ) * x + (3 : ℤ) := by
    simp only [innerRatio]; push_cast; ring
  have h40 : x + 40 = x + (40 : ℤ) := by push_cast; ring
  rw [secondPeriodicAntideriv, secondPeriodicAntideriv, h, Int.fract_add_intCast, h40,
    Int.fract_add_intCast]

/-- `𝒫₂` is periodic of period `40`. -/
theorem periodic_secondPeriodicAntideriv : Function.Periodic secondPeriodicAntideriv 40 :=
  secondPeriodicAntideriv_add_forty

end Zeta5Irr
