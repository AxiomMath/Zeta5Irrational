/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.EllXz
public import Zeta5Irr.ExactIntegrals.ExPsi

/-!
# The deviation `δ(x, z) = ℓ(x, z) - 2x`

The integer `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1` is within `1` of `2x`. Its deviation
`δ(x, z) = ℓ(x, z) - 2x` measures the step structure of the pole counts: it is a bounded,
`1`-periodic function of `x`, even in `z`, with values in `(-1, 1]`.

## Main definitions

* `Zeta5Irr.ellDeviation`: `δ(x, z) = ℓ(x, z) - 2x`.

## Main results

* `Zeta5Irr.ellDeviation_eq_psi`: `δ` is the function `Ψ` of `Zeta5Irr.ExactIntegrals.ExPsi`
  (definitionally), whose API (bounds, periodicity, parity, integrability) applies to `δ`.

## Implementation notes

* The source states the definition for `0 < z < 1/2`. The formula makes sense for all real
  `x` and `z`, so `δ` is defined on `ℝ × ℝ`, and the constraint on `z` is a hypothesis of the
  results that need it. None of the lemmas in this file need it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2: the step structure of the pole counts.
-/

@[expose] public section

namespace Zeta5Irr

/-- The deviation `δ(x, z) = ℓ(x, z) - 2x` of the integer `ℓ(x, z)` from `2x`, for all
real `x` and `z`. -/
@[zeta5irr "def_norm_delta"]
noncomputable def ellDeviation (x z : ℝ) : ℝ := ell x z - 2 * x

/-- `δ(x, z) = ℓ(x, z) - 2x`. -/
theorem ellDeviation_def (x z : ℝ) : ellDeviation x z = ell x z - 2 * x := rfl

/-- The deviation `δ` is the function `Ψ` of the exact integrals: `δ(x, z) = Ψ_x(z)`. -/
theorem ellDeviation_eq_psi : ellDeviation = psi := rfl

end Zeta5Irr
