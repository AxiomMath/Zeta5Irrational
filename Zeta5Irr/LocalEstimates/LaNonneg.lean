/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La
public import Zeta5Irr.LocalEstimates.InTLower
public import Zeta5Irr.LocalEstimates.InBaBound

/-!
# The class dimensions `L_a` are at least two

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, let `p` be a prime with `K / M < p ≤ K / 3` and let
`1 ≤ a ≤ m°`. Then the class dimension `L_a = T - b_a + ε_a` satisfies `L_a ≥ 2`.

Put `x = K / p`, so that `x ≥ 3`. Since `ε_a ≥ 0`, `L_a ≥ T - b_a`, and the bounds
`T > 2 H x - 21 / 20` and `b_a ≤ 6 α x + 3` give
`L_a > 2 (1 - α) x - 81 / 20 = 2 λ x - 81 / 20 ≥ 3 / 2`. As `L_a` is an integer, `L_a ≥ 2`.

## Main results

* `Zeta5Irr.two_le_innerClassDim`: `2 ≤ L_a`.

## Implementation notes

* The source assumes that `p` is prime. This hypothesis is not used, since neither of the
  bounds on `T` and `b_a` needs it, and it is therefore dropped.
* The hypothesis `K ∈ 40 ℤ_{>0}` is built into the parametrisation `K = 40 n`; positivity of
  `n` follows from `K ≥ 200 M²`.
* The hypotheses `K / M < p ≤ K / 3` are stated in `ℚ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3 (The inner range: dimensions).
-/

@[expose] public section

namespace Zeta5Irr

/-- **The class dimensions are at least two.** For `M ≥ 40`, `K = 40 n ≥ 200 M²`,
`K / M < p ≤ K / 3` and `1 ≤ a ≤ m°`, the class dimension satisfies `2 ≤ L_a`. -/
@[zeta5irr "lem_La_nonneg"]
theorem two_le_innerClassDim {n p M a : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hpl : (poleBound n : ℚ) / M < p) (hpu : (p : ℚ) ≤ poleBound n / 3) (ha : 1 ≤ a)
    (ham : a ≤ mStar p) : 2 ≤ innerClassDim n p M a := by
  have hT := commonClassDim_gt hM hK hpl
  have hb := innerClassOrder_innerDegree_le (n := n) ha ham
  have hL := sub_innerClassOrder_le_innerClassDim n p M a
  have hp : (0 : ℚ) < p := by
    rw [mStar_def] at ham
    exact_mod_cast (by omega : 0 < p)
  have hx : (3 : ℚ) ≤ poleBound n / p := by
    rw [le_div_iff₀ hp]
    linarith
  have hL' : ((commonClassDim n p M - innerClassOrder p (innerDegree n) a : ℤ) : ℚ) ≤
      innerClassDim n p M a := by exact_mod_cast hL
  have key : (3 / 2 : ℚ) < innerClassDim n p M a := by
    rw [Int.cast_sub, Int.cast_natCast] at hL'
    simp only [heightRatio, innerRatio, mul_div_assoc] at hT hb
    linarith
  have : (1 : ℤ) < innerClassDim n p M a := by
    have : (1 : ℚ) < innerClassDim n p M a := by linarith
    exact_mod_cast this
  omega

end Zeta5Irr
