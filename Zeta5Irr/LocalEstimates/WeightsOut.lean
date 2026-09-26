/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.EllA
public import Zeta5Irr.LocalEstimates.OutDelta
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# The ordinary entry valuations `w_{a,i}` of the outer range

For a prime `p`, a class `1 ≤ a ≤ m°` and an index `0 ≤ i < ℓ_K(a) - δ_a`, the entry
valuations of the outer range are
`w_{a,i} = min(0, i + 3 δ_a - (ℓ_K(a) + 4) / 2)` if `i < ℓ_K(a) - 2`, and `w_{a,i} = 0` if
`i ≥ ℓ_K(a) - 2`.

## Main definitions

* `Zeta5Irr.outerWeight`: the entry valuation `w_{a,i}`.

## Main results

* `Zeta5Irr.outerWeight_of_lt`: the formula `min(0, i + 3 δ_a - (ℓ_K(a) + 4) / 2)` for
  `i < ℓ_K(a) - 2`.
* `Zeta5Irr.outerWeight_of_le`: `w_{a,i} = 0` for `ℓ_K(a) - 2 ≤ i`.
* `Zeta5Irr.outerWeight_nonpos`: every `w_{a,i}` is nonpositive.
* `Zeta5Irr.two_mul_outerWeight_eq`: `2 w_{a,i}` is the integer
  `min(0, 2 i + 6 δ_a - ℓ_K(a) - 4)` or `0`.
* `Zeta5Irr.outerWeight_eq_zero_iff`: `w_{a,i} = 0` iff `ℓ_K(a) - 2 ≤ i` or
  `ℓ_K(a) + 4 ≤ 2 i + 6 δ_a`.
* `Zeta5Irr.exists_int_two_mul_outerWeight`: `2 w_{a,i}` is an integer.

## Implementation notes

* The value is rational, since `(ℓ_K(a) + 4) / 2` is a half-integer when `ℓ_K(a)` is odd.
* The data `p`, `K` and the threshold `N` of `δ_a` are explicit arguments, and `a` is an
  integer, matching `Zeta5Irr.ellA` and `Zeta5Irr.outerDelta`. The source's ranges
  `1 ≤ a ≤ m°` and `i < ℓ_K(a) - δ_a` are not needed to write the formula down, so the
  definition is total and the lemmas assume only what they use.
* The case split `i < ℓ_K(a) - 2` uses truncated subtraction in `ℕ`; when `ℓ_K(a) < 2` it
  selects the second branch, as the source's comparison in `ℤ` does.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10: the outer range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

/-- The ordinary entry valuation `w_{a,i}` of the outer range: equal to
`min(0, i + 3 δ_a - (ℓ_K(a) + 4) / 2)` if `i < ℓ_K(a) - 2`, and to `0` otherwise. Here
`ℓ_K = ellA p K` and `δ_a = outerDelta N a`. -/
@[zeta5irr "def_weights_out"]
def outerWeight (p K : ℕ) (N a : ℤ) (i : ℕ) : ℚ :=
  if i < ellA p K a - 2 then
    min 0 ((i : ℚ) + 3 * outerDelta N a - ((ellA p K a : ℚ) + 4) / 2)
  else 0

/-- For `i < ℓ_K(a) - 2`, `w_{a,i} = min(0, i + 3 δ_a - (ℓ_K(a) + 4) / 2)`. -/
theorem outerWeight_of_lt {p K : ℕ} {N a : ℤ} {i : ℕ} (h : i < ellA p K a - 2) :
    outerWeight p K N a i =
      min 0 ((i : ℚ) + 3 * outerDelta N a - ((ellA p K a : ℚ) + 4) / 2) := by
  simp [outerWeight, h]

/-- For `ℓ_K(a) - 2 ≤ i`, `w_{a,i} = 0`. -/
theorem outerWeight_of_le {p K : ℕ} {N a : ℤ} {i : ℕ} (h : ellA p K a - 2 ≤ i) :
    outerWeight p K N a i = 0 := by
  simp [outerWeight, h.not_gt]

/-- Every entry valuation `w_{a,i}` is nonpositive. -/
theorem outerWeight_nonpos (p K : ℕ) (N a : ℤ) (i : ℕ) : outerWeight p K N a i ≤ 0 := by
  unfold outerWeight
  split_ifs
  exacts [min_le_left _ _, le_rfl]

/-- Twice the entry valuation is an explicit integer: `2 w_{a,i}` equals
`min(0, 2 i + 6 δ_a - ℓ_K(a) - 4)` if `i < ℓ_K(a) - 2` and `0` otherwise. -/
theorem two_mul_outerWeight_eq (p K : ℕ) (N a : ℤ) (i : ℕ) :
    2 * outerWeight p K N a i =
      ((if i < ellA p K a - 2 then
        min 0 (2 * (i : ℤ) + 6 * outerDelta N a - ellA p K a - 4) else 0 : ℤ) : ℚ) := by
  unfold outerWeight
  split_ifs
  · push_cast
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 2)]
    congr 1 <;> ring
  · simp

/-- The entry valuation `w_{a,i}` vanishes if and only if `ℓ_K(a) - 2 ≤ i` or
`ℓ_K(a) + 4 ≤ 2 i + 6 δ_a`. -/
theorem outerWeight_eq_zero_iff {p K : ℕ} {N a : ℤ} {i : ℕ} :
    outerWeight p K N a i = 0 ↔
      ellA p K a - 2 ≤ i ∨ ellA p K a + 4 ≤ 2 * i + 6 * outerDelta N a := by
  rw [← mul_eq_zero_iff_left (two_ne_zero' ℚ), two_mul_outerWeight_eq, Int.cast_eq_zero]
  split_ifs with h
  · rw [min_eq_left_iff]
    omega
  · simp only [true_iff]
    omega

/-- Twice the entry valuation `w_{a,i}` is an integer. -/
theorem exists_int_two_mul_outerWeight (p K : ℕ) (N a : ℤ) (i : ℕ) :
    ∃ z : ℤ, 2 * outerWeight p K N a i = z :=
  ⟨_, two_mul_outerWeight_eq p K N a i⟩

end Zeta5Irr
