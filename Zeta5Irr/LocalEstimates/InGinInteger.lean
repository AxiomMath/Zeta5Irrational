/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.GammaIn

/-!
# The inner exponent `γ_p^in` is an integer

For an odd prime `p` and an integer `M ≥ 40`, the inner exponent
`γ_p^in = 2 ∑_{a=0}^{m°} ∑_{i=0}^{L_a - 1} w_{a,i}` is an integer. Indeed every doubled weight
`2 w_{a,i}` is an integer: for `a ≥ 1` it is `2 i + 2 b_a - ℓ_K(a) - 4`, and for `a = 0` it is
the minimum of `4 i + 12 m_N - 2 m_K + 1` and of the integers `2 Z_c - ℓ_K(c) - 4`,
`1 ≤ c ≤ m°`.

## Main results

* `Zeta5Irr.exists_two_mul_innerWeight_eq_intCast`: `2 w_{a,i}` is an integer.
* `Zeta5Irr.exists_innerExponent_eq_intCast`: `γ_p^in` is an integer.

## Implementation notes

The hypotheses that `p` is an odd prime and `M ≥ 40` are not needed: the weights are defined
for all `p`, `M`, `a`, `i`, with the minimum in the case `a = 0` a `Finset.fold min` starting
from `2 i + 6 m_N - m_K + 1/2`, so no nonemptiness of `{1, …, m°}` is required.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6 (The inner range: the weights).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The doubled weight `2 w_{a,i}` of the inner range is an integer. -/
theorem exists_two_mul_innerWeight_eq_intCast (n p M a i : ℕ) :
    ∃ z : ℤ, 2 * innerWeight n p M a i = z := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [innerWeight_zero_eq_fold]
    induction Icc 1 (mStar p) using Finset.induction_on with
    | empty =>
      exact ⟨4 * i + 12 * mA p (innerDegree n) - 2 * mA p (poleBound n) + 1, by
        simp only [fold_empty]
        generalize mA p (innerDegree n) = x
        generalize mA p (poleBound n) = y
        push_cast; ring⟩
    | insert c s hc ih =>
      rw [fold_insert hc]
      rcases min_choice ((classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2)
        (s.fold min (2 * (i : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2)
          (fun c => (classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2))
        with h | h
      · exact ⟨2 * classDim n p M c - ellA p (poleBound n) c - 4, by
          rw [h]; push_cast; ring⟩
      · rw [h]; exact ih
  · exact ⟨2 * i + 2 * innerClassOrder p (innerDegree n) a - ellA p (poleBound n) a - 4, by
      rw [innerWeight_of_ne_zero _ _ _ ha]; push_cast; ring⟩

/-- **The inner exponent is an integer**: `γ_p^in ∈ ℤ`. -/
@[zeta5irr "lem_in_gin_integer"]
theorem exists_innerExponent_eq_intCast (n p M : ℕ) :
    ∃ z : ℤ, innerExponent n p M = z := by
  choose w hw using fun a i => exists_two_mul_innerWeight_eq_intCast n p M a i
  refine ⟨∑ a ∈ range (mStar p + 1),
    ∑ i ∈ range (rowPolyExponent n p M a), w a i, ?_⟩
  rw [innerExponent, mul_sum]
  push_cast
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun i _ => hw a i

end Zeta5Irr
