/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormP2

/-!
# Continuity of the second periodic antiderivative `𝒫₂`

The second periodic antiderivative `𝒫₂(x) = (74 / α) G₀({α x}) - λ G₀({x})` is continuous on
all of `ℝ`. Although the fractional part `x ↦ {c x}` jumps from `1` to `0` at each point of
`c⁻¹ ℤ`, the cubic kernel `G₀` takes the same value `0` at both ends of `[0, 1]`, so each
composite `x ↦ G₀({c x})` is continuous, and `𝒫₂` is a linear combination of two of them.

## Main results

* `Zeta5Irr.continuous_cubicKernel_fract`: `x ↦ G₀({x})` is continuous.
* `Zeta5Irr.continuous_secondPeriodicAntideriv`: `𝒫₂` is continuous.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9: the tail integral.
-/

@[expose] public section

namespace Zeta5Irr

/-- The cubic kernel composed with the fractional part, `x ↦ G₀({x})`, is continuous, since
`G₀(0) = G₀(1)`. -/
theorem continuous_cubicKernel_fract : Continuous fun x : ℝ => cubicKernel (Int.fract x) :=
  continuous_cubicKernel.continuousOn.comp_fract'' (by simp)

/-- The second periodic antiderivative `𝒫₂` is continuous on `ℝ`. -/
@[zeta5irr "lem_norm_P2_cont"]
theorem continuous_secondPeriodicAntideriv : Continuous secondPeriodicAntideriv := by
  unfold secondPeriodicAntideriv
  have h := continuous_cubicKernel_fract
  exact (continuous_const.mul (h.comp (continuous_const.mul continuous_id))).sub
    (continuous_const.mul h)

end Zeta5Irr
