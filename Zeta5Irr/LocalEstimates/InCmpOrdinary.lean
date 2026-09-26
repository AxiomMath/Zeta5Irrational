/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La
public import Zeta5Irr.LocalEstimates.WeightsIn
public import Zeta5Irr.LocalEstimates.InEllSpread
public import Zeta5Irr.LocalEstimates.InEpsOrder

/-!
# Comparison of the ordinary inner weights with the class bounds

For an odd prime `p`, an integer `M ≥ 40`, indices `1 ≤ a, s ≤ m°` and `0 ≤ i < L_a`, the
weight `w_{a,i} = i + b_a - (ℓ_K(a) + 4) / 2` of the inner range is at most
`Z_s - (ℓ_K(s) + 4) / 2`.

Indeed `L_a + b_a = Z_a`, so `w_{a,i} ≤ Z_a - 1 - (ℓ_K(a) + 4) / 2`, and it remains to see
that `Z_s - Z_a + 1 + (ℓ_K(a) - ℓ_K(s)) / 2 ≥ 0`. Here `Z_s - Z_a = ε_s - ε_a` with
`ε_a, ε_s ∈ {0, 1}`. If `ε_s ≥ ε_a`, this follows from `|ℓ_K(a) - ℓ_K(s)| ≤ 1`; otherwise
`ε_a = 1`, `ε_s = 0`, and then `ℓ_K(a) ≥ ℓ_K(s)`.

## Main results

* `Zeta5Irr.innerWeight_le_classDim_sub`: `w_{a,i} ≤ Z_s - (ℓ_K(s) + 4) / 2`.

## Implementation notes

* The source assumes `M ≥ 40`, `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, a prime `p` with
  `K / M < p ≤ K / 3`, and `a ≠ s`. None of these is used by the argument: the statement
  holds for every natural number `p`, every `M` and `n`, and also for `a = s` (where it
  reduces to `i + b_a < Z_a`). Here `K = 40 n` is the pole bound.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6: the inner range, the weights.
-/

@[expose] public section

namespace Zeta5Irr

/-- **Ordinary inner weights against the class bounds.** For `1 ≤ a, s ≤ m°` and
`0 ≤ i < L_a`, the weight `w_{a,i}` is at most `Z_s - (ℓ_K(s) + 4) / 2`, where `K = 40 n`. -/
@[zeta5irr "lem_in_cmp_ordinary"]
theorem innerWeight_le_classDim_sub {n p M a s i : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p)
    (hs : 1 ≤ s) (hsm : s ≤ mStar p) (hi : (i : ℤ) < innerClassDim n p M a) :
    innerWeight n p M a i ≤
      (classDim n p M s : ℚ) - ((ellA p (poleBound n) s : ℚ) + 4) / 2 := by
  rw [innerWeight_of_ne_zero n p M (by omega)]
  have hspread := abs_le.1 (abs_ellA_sub_ellA_le_one ha ham hs hsm (poleBound n))
  have hLa := innerClassDim_def n p M a
  have hZ := classDim_sub_classDim n p M s a
  have hZa := classDim_def n p M a
  have hεa := extraIndicator_le_one n p M a
  have hεs := extraIndicator_le_one n p M s
  have key : 2 * ((i : ℤ) + innerClassOrder p (innerDegree n) a) -
      (ellA p (poleBound n) a : ℤ) ≤
      2 * classDim n p M s - (ellA p (poleBound n) s : ℤ) := by
    by_cases h : extraIndicator n p M a ≤ extraIndicator n p M s
    · omega
    · have : (ellA p (poleBound n) s : ℤ) ≤ ellA p (poleBound n) a := by
        exact_mod_cast ellA_le_of_extraIndicator (n := n) (M := M) (by omega) (by omega)
      omega
  have key' := (Int.cast_le (R := ℚ)).2 key
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast] at key'
  linarith

end Zeta5Irr
