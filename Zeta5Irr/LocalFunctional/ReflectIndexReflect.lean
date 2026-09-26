/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.ReflectIndex

/-!
# The reflected index is invariant under `r ↦ -1 - r`

The reflected index `d : ℤ → ℕ`, with `d(r) = r` for `r ≥ 0` and `d(r) = -r - 1` for `r < 0`,
satisfies `d(-1 - r) = d(r)` for every integer `r`: the reflection `r ↦ -1 - r` exchanges the
natural numbers with the negative integers, and `d` undoes it on the negative side.

## Main results

* `Zeta5Irr.reflectIndex_neg_one_sub`: `d(-1 - r) = d(r)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

/-- The reflected index is invariant under the reflection `r ↦ -1 - r`: `d(-1 - r) = d(r)`. -/
@[zeta5irr "lem_tau_dr_reflect"]
theorem reflectIndex_neg_one_sub (r : ℤ) : reflectIndex (-1 - r) = reflectIndex r := by
  rcases le_or_gt 0 r with hr | hr
  · have h := reflectIndex_of_neg (show -1 - r < 0 by omega)
    have h' := reflectIndex_of_nonneg hr
    omega
  · have h := reflectIndex_of_nonneg (show 0 ≤ -1 - r by omega)
    have h' := reflectIndex_of_neg hr
    omega

end Zeta5Irr
