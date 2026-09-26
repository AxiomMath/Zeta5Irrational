/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Gamma
public import Zeta5Irr.LimitingFunctions.Ncal

/-!
# The inner limiting function `R`

For `x ≥ 3` the inner limiting function is `R(x) = -Γ(x) - 𝒩(x)`, where `Γ` is the inner
limiting function built from the integral over the half-period `[0, 1/2]` and `𝒩` is the
scalar limiting function. Its weighted integral `∫ R(x) / x³ dx` is evaluated exactly.

## Main definitions

* `Zeta5Irr.innerLimitingR`: the function `R`.

## Main results

* `Zeta5Irr.innerLimitingR_def`: the defining formula `R(x) = -Γ(x) - 𝒩(x)`.

## Implementation notes

* The source defines `R` only for `x ≥ 3`. Both `Γ` and `𝒩` are defined on all of `ℝ`, so
  `R` is defined on all of `ℝ`; this lets integrals of `R(x) / x³` over intervals and
  half-lines be stated directly, and the restriction `x ≥ 3` is carried by the lemmas that
  use it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1 (The inner limiting function).
-/

@[expose] public section

namespace Zeta5Irr

/-- The inner limiting function `R(x) = -Γ(x) - 𝒩(x)`, where `Γ` is
`innerLimitingGamma` and `𝒩` is `scalarLimitingFunction`.
The source restricts to `x ≥ 3`; the formula is used for all real `x`. -/
@[zeta5irr "def_R"]
noncomputable def innerLimitingR (x : ℝ) : ℝ :=
  -innerLimitingGamma x - scalarLimitingFunction x

/-- Unfolding lemma for `R`. -/
theorem innerLimitingR_def (x : ℝ) :
    innerLimitingR x = -innerLimitingGamma x - scalarLimitingFunction x :=
  rfl

end Zeta5Irr
