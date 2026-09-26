/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsIn
public import Zeta5Irr.LocalEstimates.La

/-!
# The sum of the weights over a block of the inner range

For `1 ≤ a ≤ m°` the weights of the block of the inner range indexed by `a` are
`w_{a,i} = i + b_a - (ℓ_K(a) + 4) / 2` for `0 ≤ i < L_a`. Summing the arithmetic progression and
using `L_a = Z_a - b_a` gives the closed form
`2 ∑_{i=0}^{L_a-1} w_{a,i} = (Z_a - b_a) (Z_a + b_a - ℓ_K(a) - 5)`.

## Main results

* `Zeta5Irr.two_mul_sum_innerWeight`: the closed form above.

## Implementation notes

* Since `L_a` is an integer, the sum runs over `i ∈ range L_a.toNat`. The only hypotheses used
  are `a ≠ 0` and `0 ≤ L_a`; the latter holds under the standing hypotheses of the source, by
  `Zeta5Irr.two_le_innerClassDim`. The remaining standing hypotheses (`p` an odd prime,
  `M ≥ 40`, `a ≤ m°`, …) are not needed and are dropped.
* The identity `L_a = Z_a - b_a` is `Zeta5Irr.innerClassDim_eq_classDim_sub`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- `L_a = Z_a - b_a`. -/
theorem innerClassDim_eq_classDim_sub (n p M a : ℕ) :
    innerClassDim n p M a = classDim n p M a - innerClassOrder p (innerDegree n) a := by
  rw [innerClassDim_def, classDim_def]
  ring

/-- **The block weight sum.** For `a ≠ 0` with `0 ≤ L_a`,
`2 ∑_{i=0}^{L_a-1} w_{a,i} = (Z_a - b_a) (Z_a + b_a - ℓ_K(a) - 5)`. -/
@[zeta5irr "lem_norm_block_sum"]
theorem two_mul_sum_innerWeight {n p M a : ℕ} (ha : a ≠ 0) (hL : 0 ≤ innerClassDim n p M a) :
    2 * ∑ i ∈ range (innerClassDim n p M a).toNat, innerWeight n p M a i =
      ((classDim n p M a : ℚ) - innerClassOrder p (innerDegree n) a) *
        ((classDim n p M a : ℚ) + innerClassOrder p (innerDegree n) a -
          ellA p (poleBound n) a - 5) := by
  have hZ : (classDim n p M a : ℚ) =
      ((innerClassDim n p M a).toNat : ℚ) + innerClassOrder p (innerDegree n) a := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hL, innerClassDim_eq_classDim_sub]
    push_cast
    ring
  simp_rw [innerWeight_of_ne_zero n p M ha]
  rw [hZ]
  generalize (innerClassDim n p M a).toNat = L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

end Zeta5Irr
