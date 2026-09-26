/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Zeta5Irr.LocalFunctional.ReflectIndex
public import Mathlib.Tactic.ENatToNat

/-!
# The difference identity for `H_{d(r)}^{(5)}`

For every integer `r ≠ 0` the harmonic sums at the reflected indices of `r - 1` and `r` differ by
one term: `H_{d(r-1)}^{(5)} - H_{d(r)}^{(5)} = -r⁻⁵`. For `r ≥ 1` this is the recurrence of the
harmonic sum at `d(r) = r`; for `r ≤ -1` one has `d(r - 1) = d(r) + 1 = -r`, and the recurrence
gives `(-r)⁻⁵ = -r⁻⁵`, the fifth power being odd.

## Main results

* `Zeta5Irr.harmonicFive_reflectIndex_sub_one_sub`:
  `H_{d(r-1)}^{(5)} - H_{d(r)}^{(5)} = -r⁻⁵` for every `r ∈ ℤ`.

## Implementation notes

The source assumes `r ≠ 0`. The hypothesis is dropped here: at `r = 0` both indices are
`d(-1) = d(0) = 0`, so the left side vanishes, and so does the right side, since `0⁻¹ = 0` in `ℚ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the reflection and difference identities).
-/

@[expose] public section

namespace Zeta5Irr

/-- `H_{d(r-1)}^{(5)} - H_{d(r)}^{(5)} = -r⁻⁵` for every integer `r`. The source states this for
`r ≠ 0`; at `r = 0` both sides vanish. -/
@[zeta5irr "lem_tau_harm_incr"]
theorem harmonicFive_reflectIndex_sub_one_sub (r : ℤ) :
    harmonicFive (reflectIndex (r - 1)) - harmonicFive (reflectIndex r) = -((r : ℚ) ^ 5)⁻¹ := by
  cases r with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast]
    cases n with
    | zero => simp [show reflectIndex (-1) = 0 from rfl, show reflectIndex 0 = 0 from rfl]
    | succ m =>
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring, reflectIndex_natCast,
        reflectIndex_natCast, harmonicFive_succ]
      push_cast
      ring
  | negSucc n =>
    rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) from rfl, reflectIndex_negSucc,
      reflectIndex_negSucc, harmonicFive_succ, Int.cast_negSucc]
    push_cast
    rw [show (-((n : ℚ) + 1)) ^ 5 = -((n : ℚ) + 1) ^ 5 from Odd.neg_pow ⟨2, rfl⟩ _, inv_neg]
    ring

end Zeta5Irr
