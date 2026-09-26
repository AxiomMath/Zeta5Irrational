/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The inner limiting function `T̃`

The inner limiting function is the step function `T̃(x) = ⌊2 H x⌋`, where `H = 23/20` is the
height ratio. It is the limiting shape, after rescaling by `K`, of the upper end of the inner
range of summation, and enters the later limiting integrands through products such as
`(T̃ - b)(T̃ + b - ℓ - 5)`.

## Main definitions

* `Zeta5Irr.innerLimit`: the inner limiting function `T̃(x) = ⌊2 H x⌋`.

## Implementation notes

* The source defines `T̃` only for `x ≥ 3`. The formula makes sense for every real `x`, so
  `T̃` is defined on all of `ℝ`, and the restriction `x ≥ 3` is carried by the lemmas that
  use it.
* `T̃` takes integer values but is real-valued, the coercion of `Int.floor`, because it is
  always combined with real quantities.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6.1: the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The inner limiting function `T̃(x) = ⌊2 H x⌋`, where `H = 23/20` is the height ratio. -/
@[zeta5irr "def_Tx"]
noncomputable def innerLimit (x : ℝ) : ℝ := ⌊2 * (heightRatio : ℝ) * x⌋

/-- `T̃(x) = ⌊2 H x⌋`, where `H = 23/20` is the height ratio. -/
theorem innerLimit_def (x : ℝ) : innerLimit x = ⌊2 * (heightRatio : ℝ) * x⌋ := rfl

end Zeta5Irr
