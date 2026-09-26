/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.V
public import Zeta5Irr.Measure.VLogIntegral

/-!
# A closed form for the external field `V`

For `t > 0` the external field
`V(t) = 2π√t + ∫₀¹ log (t + u²) du - 6 ∫₀^α log (t + u²) du`, with `α = 3/40`, has the closed
form
`V(t) = log (1 + t) - 6 α log (t + α²) - 2 + 12 α
  + 2 √t (π + arctan (1 / √t) - 6 arctan (α / √t))`.
It follows by evaluating both integrals with the closed form of `∫₀^c log (t + u²) du`, at
`c = 1` and `c = α`, and collecting the terms carrying a factor `√t`.

## Main results

* `Zeta5Irr.externalField_eq`: the closed form of `V(t)` for `t > 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For `t > 0`, the external field has the closed form
`V(t) = log (1 + t) - 6 α log (t + α²) - 2 + 12 α
  + 2 √t (π + arctan (1 / √t) - 6 arctan (α / √t))`, where `α = 3/40` is the inner ratio. -/
@[zeta5irr "lem_V_formula"]
theorem externalField_eq {t : ℝ} (ht : 0 < t) :
    externalField t =
      log (1 + t) - 6 * (innerRatio : ℝ) * log (t + (innerRatio : ℝ) ^ 2) - 2 +
        12 * (innerRatio : ℝ) +
        2 * √t * (π + arctan (1 / √t) - 6 * arctan ((innerRatio : ℝ) / √t)) := by
  rw [externalField, integral_log_add_sq ht, integral_log_add_sq ht]
  rw [one_pow, add_comm t 1]
  ring

end Zeta5Irr
