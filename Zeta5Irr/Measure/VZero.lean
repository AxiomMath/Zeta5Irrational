/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.V

/-!
# The external field at the origin

At `t = 0` the term `2π√t` of the external field `V` vanishes and its integrands reduce to
`log (u²) = 2 log u`, so the closed form `∫ₐᵇ log s ds = b log b - a log a - b + a` gives
`V(0) = -12 α log α - 2 + 12 α`, where `α = 3/40` is the inner ratio.

## Main results

* `Zeta5Irr.integral_log_sq`: `∫₀^c log (u²) du = 2 (c log c - c)`.
* `Zeta5Irr.externalField_zero`: `V(0) = -12 α log α - 2 + 12 α`.

## Implementation notes

* The source uses `c > 0` in the evaluation of `∫₀^c log (u²) du`; the identity holds for
  every real `c`, since `log (u²) = 2 log u` for every real `u` under the convention
  `log x = log |x|`, and it is stated here without that hypothesis.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For every real `c`, `∫₀^c log (u²) du = 2 (c log c - c)`. -/
theorem integral_log_sq (c : ℝ) :
    ∫ u in (0 : ℝ)..c, log (u ^ 2) = 2 * (c * log c - c) := by
  simp_rw [Real.log_pow]
  rw [intervalIntegral.integral_const_mul, integral_log]
  push_cast
  simp

/-- The value of the external field at the origin: `V(0) = -12 α log α - 2 + 12 α`, where
`α = 3/40` is the inner ratio. -/
@[zeta5irr "lem_V_zero"]
theorem externalField_zero :
    externalField 0 =
      -12 * (innerRatio : ℝ) * log innerRatio - 2 + 12 * (innerRatio : ℝ) := by
  simp only [externalField, sqrt_zero, mul_zero, zero_add, integral_log_sq, log_one]
  ring

end Zeta5Irr
