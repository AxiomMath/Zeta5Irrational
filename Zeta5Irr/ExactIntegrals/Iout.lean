/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExOuterIntegrand

/-!
# The outer integral `I_out`

The outer integral is the definite integral
$$I_{\mathrm{out}} = \int_{1/3}^{2\lambda} \Theta(y)\,dy$$
of the outer integrand `Θ` over `[1/3, 2λ]`, where `λ = 37/40` is the order ratio, so that
the upper endpoint is `2λ = 37/20`. Beyond `2λ` the integrand vanishes identically.

## Main definitions

* `Zeta5Irr.outerIntegral`: the real number `I_out`.

## Main results

* `Zeta5Irr.outerIntegral_eq`: `I_out = ∫_{1/3}^{37/20} Θ(y) dy`, with the upper endpoint
  evaluated.

## Implementation notes

The integral is Mathlib's interval integral `∫ y in a..b, f y` against Lebesgue measure.
`I_out` is a fixed number (it does not depend on `n`), so it is a nullary constant.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.4 (The outer integral).
-/

@[expose] public section

namespace Zeta5Irr

/-- The outer integral `I_out = ∫_{1/3}^{2λ} Θ(y) dy`, where `Θ` is the outer integrand and
`λ = 37/40` the order ratio. -/
@[zeta5irr "def_Iout"]
noncomputable def outerIntegral : ℝ :=
  ∫ y in (1 / 3 : ℝ)..(2 * (orderRatio : ℝ)), outerIntegrand y

/-- The outer integral with its upper endpoint evaluated: `I_out = ∫_{1/3}^{37/20} Θ(y) dy`. -/
theorem outerIntegral_eq : outerIntegral = ∫ y in (1 / 3 : ℝ)..(37 / 20), outerIntegrand y := by
  rw [outerIntegral]
  congr 1
  norm_num [orderRatio]

end Zeta5Irr
