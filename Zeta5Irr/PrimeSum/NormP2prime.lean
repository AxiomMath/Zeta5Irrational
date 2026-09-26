/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormP2
public import Zeta5Irr.PrimeSum.NormPper

/-!
# The derivative of the second periodic antiderivative `𝒫₂`

Away from its breakpoints `ℤ ∪ α⁻¹ ℤ`, the second periodic antiderivative
`𝒫₂(x) = (74 / α) G₀({α x}) - λ G₀({x})` is differentiable, with
`𝒫₂'(x) = 𝒫(x) - 2923/240`, where `𝒫` is the first periodic antiderivative.

The proof is the chain rule: off `c⁻¹ ℤ` the function `x ↦ {c x}` has derivative `c`, since
the floor is locally constant there, and `G₀'(v) = v (1 - v) - 1/6`. The two constants
combine to `(74 - λ) / 6 = 2923/240`.

## Main results

* `Zeta5Irr.hasDerivAt_secondPeriodicAntideriv`: for `x ∉ ℤ ∪ α⁻¹ ℤ`,
  `𝒫₂'(x) = 𝒫(x) - 2923/240`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9: the tail integral.
-/

@[expose] public section

namespace Zeta5Irr

/-- Away from `ℤ ∪ α⁻¹ ℤ`, the second periodic antiderivative is differentiable with
`𝒫₂'(x) = 𝒫(x) - 2923/240`. -/
@[zeta5irr "lem_norm_P2prime"]
theorem hasDerivAt_secondPeriodicAntideriv {x : ℝ} (hx : ∀ m : ℤ, x ≠ m)
    (hαx : ∀ m : ℤ, x ≠ (innerRatio : ℝ)⁻¹ * m) :
    HasDerivAt secondPeriodicAntideriv (firstPeriodicAntideriv x - 2923 / 240) x := by
  have hα : (innerRatio : ℝ) ≠ 0 := by norm_num [innerRatio]
  have hαx' : (innerRatio : ℝ) * x ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨m, h⟩
    apply hαx m
    rw [h, inv_mul_cancel_left₀ hα]
  have h1 : HasDerivAt (fun y : ℝ => Int.fract ((innerRatio : ℝ) * y)) (1 * innerRatio) x :=
    (hasDerivAt_fract hαx').comp x ((hasDerivAt_id x).const_mul _ |>.congr_deriv (by simp))
  have h2 := ((hasDerivAt_cubicKernel _).comp x h1).const_mul (74 / (innerRatio : ℝ))
  have h3 := ((hasDerivAt_cubicKernel _).comp x
    (hasDerivAt_fract fun ⟨m, hm⟩ ↦ hx m hm.symm)).const_mul (orderRatio : ℝ)
  refine (h2.sub h3).congr_deriv ?_
  simp only [firstPeriodicAntideriv, orderRatio]
  field_simp
  push_cast
  ring

/-- Away from `ℤ ∪ α⁻¹ ℤ`, `𝒫₂'(x) = 𝒫(x) - 2923/240`, as a `deriv` identity. -/
theorem deriv_secondPeriodicAntideriv {x : ℝ} (hx : ∀ m : ℤ, x ≠ m)
    (hαx : ∀ m : ℤ, x ≠ (innerRatio : ℝ)⁻¹ * m) :
    deriv secondPeriodicAntideriv x = firstPeriodicAntideriv x - 2923 / 240 :=
  (hasDerivAt_secondPeriodicAntideriv hx hαx).deriv

end Zeta5Irr
