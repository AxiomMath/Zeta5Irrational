/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotM0Notation
public import Zeta5Irr.Measure.RhoEnergyEnclosure
public import Zeta5Irr.Measure.CstarEnclosure
public import Zeta5Irr.ExactIntegrals.U

/-!
# The energy margin bounds the energy combination

With `λ = 37/40`, `M₀ = -1329/200`, `ρ` the comparison measure and `C_*` the norm constant,
$$\lambda M_0 - I(\rho) + C_* \le U = -\frac{2733991}{2000000}.$$
Indeed `λ M₀ = -49173/8000` exactly, while the enclosures of `I(ρ)` and `C_*` give
`-I(ρ) < 2126593445148 / 10¹²` and `C_* < 2653035990341 / 10¹²`; the sum of the three bounds
is `-1366995564511 / 10¹²`, which is below `U = -1366995500000 / 10¹²`.

## Main results

* `Zeta5Irr.orderRatio_mul_potentialBound_sub_logEnergy_rho_add_normConstant_lt`:
  the strict inequality `λ M₀ - I(ρ) + C_* < U`.
* `Zeta5Irr.orderRatio_mul_potentialBound_sub_logEnergy_rho_add_normConstant_le`:
  the non-strict inequality `λ M₀ - I(ρ) + C_* ≤ U`.

## Implementation notes

The measure `ρ` is defined on `ℝ`; its energy `I(ρ)` is that of its pushforward to `ℂ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.8 (The energy and the constant).
-/

@[expose] public section

namespace Zeta5Irr

/-- The strict form of the bound `λ M₀ - I(ρ) + C_* < U`. -/
theorem orderRatio_mul_potentialBound_sub_logEnergy_rho_add_normConstant_lt :
    (orderRatio : ℝ) * (potentialBound : ℝ) - logEnergy (rho.map ((↑) : ℝ → ℂ)) +
      normConstant < energyMargin := by
  have h1 := lt_logEnergy_rho
  have h2 := normConstant_lt
  rw [energyMargin_eq]
  norm_num [orderRatio, potentialBound]
  linarith

/-- **The energy margin bound**: `λ M₀ - I(ρ) + C_* ≤ U`. -/
@[zeta5irr "lem_U_bound"]
theorem orderRatio_mul_potentialBound_sub_logEnergy_rho_add_normConstant_le :
    (orderRatio : ℝ) * (potentialBound : ℝ) - logEnergy (rho.map ((↑) : ℝ → ℂ)) +
      normConstant ≤ energyMargin :=
  orderRatio_mul_potentialBound_sub_logEnergy_rho_add_normConstant_lt.le

end Zeta5Irr
