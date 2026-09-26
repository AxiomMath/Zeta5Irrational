/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The external field `V`

The external field of the equilibrium problem is the function `V : [0, ∞) → ℝ`,
`V(t) = 2π√t + ∫₀¹ log (t + u²) du - 6 ∫₀^α log (t + u²) du`, where `α = 3/40` is the inner
ratio. The comparison measure of this part of the argument is tested against `V` through the
potential inequality `2 U^ρ - V ≤ M₀` on `[0, ∞)`.

## Main definitions

* `Zeta5Irr.externalField`: the external field `V`.

## Implementation notes

* The source's name for the field is the single letter `V`; it is named here for what it is.
* The field is a total function `ℝ → ℝ` rather than a function on `[0, ∞)`: consumers
  differentiate `y ↦ V (y ^ 2)`, sum `V` over tuples and prove monotonicity on intervals, all
  of which are simpler without a subtype. For `t < 0` the value is a junk value, determined by
  the conventions `√t = 0` and `log x = log |x|`, and no statement depends on it.
* The integrals are interval integrals, so that the fundamental theorem of calculus and the
  closed-form evaluations of `∫ log` are available directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.1: the field, the potential, and the energy.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The external field
`V(t) = 2π√t + ∫₀¹ log (t + u²) du - 6 ∫₀^α log (t + u²) du`, where `α = 3/40` is the inner
ratio `Zeta5Irr.innerRatio`. It is meaningful for `t ≥ 0`; for `t < 0` its value is junk. -/
@[zeta5irr "def_V"]
noncomputable def externalField (t : ℝ) : ℝ :=
  2 * π * √t + (∫ u in (0 : ℝ)..1, log (t + u ^ 2)) -
    6 * ∫ u in (0 : ℝ)..(innerRatio : ℝ), log (t + u ^ 2)

end Zeta5Irr
