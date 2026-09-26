/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The norm constant `C_*`

In terms of the ratios `α = 3/40` and `λ = 37/40`, the norm constant is the real number
`C_* = -2 λ + 12 α λ (1 - log α) + 3 λ² - 2 λ² log (2 λ)`.
It is the coefficient of `K²` in the upper bound for `log S_K` that remains once the
`K² log K` terms are separated off, and it enters the final quadratic coefficient
`λ M₀ - I(ρ) + C_*` of the estimate for the linear form.

## Main definitions

* `Zeta5Irr.normConstant`: the norm constant `C_*`.

## Main results

* `Zeta5Irr.normConstant_eq`: `C_*` with the ratios substituted,
  `C_* = -37/20 + 333/400 (1 - log (3/40)) + 4107/1600 - 1369/800 log (37/20)`.

## Implementation notes

* The source's name `C_*` is not an identifier; the constant is named for the source's
  title, "the norm constant". The ratios `α` and `λ` are rational and are coerced to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6, equation (6.3): the norm constant.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- The norm constant
`C_* = -2 λ + 12 α λ (1 - log α) + 3 λ² - 2 λ² log (2 λ)`, where `α = 3/40` is
`Zeta5Irr.innerRatio` and `λ = 37/40` is `Zeta5Irr.orderRatio`. -/
@[zeta5irr "def_Cstar"]
noncomputable def normConstant : ℝ :=
  -2 * (orderRatio : ℝ) + 12 * (innerRatio : ℝ) * (orderRatio : ℝ) * (1 - log (innerRatio : ℝ)) +
    3 * (orderRatio : ℝ) ^ 2 - 2 * (orderRatio : ℝ) ^ 2 * log (2 * (orderRatio : ℝ))

/-- The norm constant with `α = 3/40` and `λ = 37/40` substituted: its only irrational
ingredients are `log (3/40)` and `log (37/20)`. -/
theorem normConstant_eq :
    normConstant = -37 / 20 + 333 / 400 * (1 - log (3 / 40)) + 4107 / 1600 -
      1369 / 800 * log (37 / 20) := by
  rw [normConstant, innerRatio, orderRatio]
  push_cast
  norm_num

end Zeta5Irr
