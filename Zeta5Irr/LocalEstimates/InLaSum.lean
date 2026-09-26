/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La
public import Zeta5Irr.LocalEstimates.InEllTotal
public import Zeta5Irr.LocalEstimates.InEpsCount
public import Mathlib.Data.Int.Star

/-!
# The class dimensions add up to `h`

For an odd prime `p` and an integer `M ≥ 40`, the reserved zero-class dimension `L₀` and the
class dimensions `L_a = T - b_a + ε_a`, `1 ≤ a ≤ m°`, add up to `h`:
`L₀ + ∑_{a=1}^{m°} L_a = h`.
Indeed `∑_a b_a = 3 ∑_a ℓ_N(a) = 3 (N - m_N)` and `∑_a ε_a = E`, so
`∑_a L_a = m° T + E - 3 (N - m_N) = h - L₀` by the definition of `E`.

## Main results

* `Zeta5Irr.zeroClassDim_add_sum_innerClassDim`: `L₀ + ∑_{a=1}^{m°} L_a = h`.

## Implementation notes

* The source assumes that `p` is an odd prime and `M ≥ 40`. The argument uses only that `p` is
  odd and `p ≥ 3`, so primality and the bound on `M` are dropped.
* The class dimensions are integers, so the identity is stated in `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For odd `p ≥ 3`, the zero-class dimension and the class dimensions add up to `h`:
`L₀ + ∑_{a=1}^{m°} L_a = h`. -/
@[zeta5irr "lem_in_La_sum"]
theorem zeroClassDim_add_sum_innerClassDim (n : ℕ) {p : ℕ} (M : ℕ) (hp : Odd p) (hp3 : 3 ≤ p) :
    (zeroClassDim M : ℤ) + ∑ a ∈ Icc 1 (mStar p), innerClassDim n p M a = matrixOrder n := by
  have hell := sum_ellA_mStar hp (innerDegree n)
  have heps := sum_extraIndicator_eq_extraCount n M hp3
  have hE := mStar_mul_commonClassDim_add_extraCount n p M
  have hmA : mA p (innerDegree n) ≤ innerDegree n := Nat.div_le_self _ _
  simp only [innerClassDim_def, sum_add_distrib, sum_sub_distrib, sum_const, Nat.card_Icc,
    add_tsub_cancel_right, nsmul_eq_mul, cast_innerClassOrder, ← mul_sum]
  push_cast at heps
  rw [heps, ← Nat.cast_sum, hell, Nat.cast_sub hmA]
  linarith
end Zeta5Irr
