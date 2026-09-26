/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La
public import Zeta5Irr.LocalEstimates.WeightsIn
public import Mathlib.Data.Int.Star

/-!
# The inner exponent `γ_p^in`

For an odd prime `p` and an integer `M ≥ 40`, the inner exponent is twice the total weight of
the inner range,
```
γ_p^in = 2 ∑_{a=0}^{m°} ∑_{i=0}^{L_a - 1} w_{a,i},
```
where `m° = (p - 1) / 2`, `L₀ = 4 M + 10` is the reserved zero-class dimension,
`L_a = T - b_a + ε_a` for `1 ≤ a ≤ m°` is the class dimension, and `w_{a,i}` are the weights
of the inner range.

## Main definitions

* `Zeta5Irr.innerExponent`: the inner exponent `γ_p^in`.

## Main results

* `Zeta5Irr.innerExponent_eq`: `γ_p^in` split into the zero class and the classes
  `1 ≤ a ≤ m°`.
* `Zeta5Irr.innerExponent_eq_of_nonneg`: the same, with the range of `i` in class `a ≥ 1` read
  as `i < L_a` for integers, when every `L_a` is nonnegative.

## Implementation notes

* The value is rational, since the weights `w_{0,i}` may be half-integers.
* The weights depend on `n` through `K = 40 n` and `N = 3 n`, so `γ_p^in` takes `n` as an
  argument along with `p` and `M`. The hypotheses that `p` is an odd prime and `M ≥ 40` are
  not needed to write the sum down, so the definition is total.
* The class dimension `L_a` for `a ≥ 1` is integer valued; the index `i` ranges over
  `0 ≤ i < L_a`, which is `Finset.range (L_a).toNat`. For `a = 0` it is `L₀`. Under the
  source's hypotheses every `L_a` is nonnegative, and then `Zeta5Irr.innerExponent_eq_of_nonneg`
  applies.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6: the inner range, the weights.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The inner exponent `γ_p^in = 2 ∑_{a=0}^{m°} ∑_{i=0}^{L_a - 1} w_{a,i}`, where `L₀` is
`Zeta5Irr.zeroClassDim`, `L_a` for `a ≥ 1` is `Zeta5Irr.innerClassDim` and `w_{a,i}` is
`Zeta5Irr.innerWeight`. -/
@[zeta5irr "def_gamma_in"]
def innerExponent (n p M : ℕ) : ℚ :=
  2 * ∑ a ∈ range (mStar p + 1),
    ∑ i ∈ range (rowPolyExponent n p M a), innerWeight n p M a i

/-- `γ_p^in = 2 (∑_{i < L₀} w_{0,i} + ∑_{a=1}^{m°} ∑_{i < L_a} w_{a,i})`. -/
theorem innerExponent_eq (n p M : ℕ) :
    innerExponent n p M = 2 * (∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i +
      ∑ a ∈ Icc 1 (mStar p), ∑ i ∈ range (innerClassDim n p M a).toNat,
        innerWeight n p M a i) := by
  rw [innerExponent, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), zero_add,
    Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc]
  congr 2
  refine sum_congr rfl fun a ha => ?_
  have : a ≠ 0 := by simp at ha; omega
  rw [rowPolyExponent_of_ne_zero _ _ _ this]

/-- If every `L_a`, `1 ≤ a ≤ m°`, is nonnegative, then
`γ_p^in = 2 (∑_{i < L₀} w_{0,i} + ∑_{a=1}^{m°} ∑_{0 ≤ i < L_a} w_{a,i})`,
with `i` ranging over the integers in `[0, L_a)`. -/
theorem innerExponent_eq_of_nonneg {n p M : ℕ}
    (h : ∀ a ∈ Icc 1 (mStar p), 0 ≤ innerClassDim n p M a) :
    innerExponent n p M = 2 * (∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i +
      ∑ a ∈ Icc 1 (mStar p), ∑ i ∈ Ico (0 : ℤ) (innerClassDim n p M a),
        innerWeight n p M a i.toNat) := by
  rw [innerExponent_eq]
  congr 2
  refine sum_congr rfl fun a ha => ?_
  obtain ⟨L, hL⟩ := Int.eq_ofNat_of_zero_le (h a ha)
  rw [hL, Int.toNat_natCast]
  refine sum_nbij' (fun i : ℕ => (i : ℤ)) Int.toNat ?_ ?_ ?_ ?_ ?_
  all_goals intro i hi
  all_goals simp_all

end Zeta5Irr
