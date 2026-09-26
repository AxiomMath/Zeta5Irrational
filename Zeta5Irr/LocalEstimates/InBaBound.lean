/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LocalEstimates.InBa
public import Zeta5Irr.LocalEstimates.InEllFormula
public import Mathlib.Data.Int.Star

/-!
# An upper bound for the inner class orders `b_a`

Let `p` be a prime and `1 ≤ a ≤ m° = (p - 1) / 2`. The inner class order is `b_a = 3 ℓ_N(a)`,
and by the closed formula for `ℓ_N(a)`,
`ℓ_N(a) = 2 m_N + 𝟙[a ≤ v_N] + 𝟙[p - a ≤ v_N]`, where `N = p m_N + v_N` with `0 ≤ v_N < p`.
If at most one indicator is `1`, then `ℓ_N(a) ≤ 2 m_N + 1 ≤ 2 N / p + 1`. If both are `1`,
then `v_N ≥ p - a ≥ (p + 1) / 2`, so `N > p (m_N + 1/2)` and `ℓ_N(a) = 2 m_N + 2 < 2 N / p + 1`.
In either case `ℓ_N(a) ≤ 2 N / p + 1`, hence `b_a ≤ 6 N / p + 3`. With `N = α K` this is
`b_a ≤ 6 α K / p + 3`.

## Main results

* `Zeta5Irr.mul_innerClassOrder_le`: the cleared-denominator bound `p b_a ≤ 6 N + 3 p`.
* `Zeta5Irr.innerClassOrder_le_of_le_mStar`: `b_a ≤ 6 N / p + 3` in any linearly ordered
  field.
* `Zeta5Irr.innerClassOrder_innerDegree_le`: `b_a ≤ 6 α K / p + 3` for `N = 3 n`,
  `K = 40 n` and `α = 3/40`.

## Implementation notes

* The source assumes `M ≥ 40`, `K ∈ 40 ℤ_{>0}`, `p` prime and `K / M < p ≤ K / 3`. None of
  these is used: the hypothesis `1 ≤ a ≤ m°` alone forces `p ≥ 3`, and the bound holds for
  every inner degree `N`. The general bound is therefore stated for arbitrary natural numbers
  `p` and `N`, and the source's form for `N = 3 n = α K` and an arbitrary `p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3 (The inner range: dimensions).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `1 ≤ a ≤ m°`, the counting function satisfies `p ℓ_N(a) ≤ 2 N + p`. -/
theorem mul_ellA_le {p a : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) (N : ℕ) :
    p * ellA p N a ≤ 2 * N + p := by
  have h2a : 2 * a < p := by rw [mStar_def] at ham; omega
  have hv : vA p N < p := vA_lt (by omega) N
  have hN := mul_mA_add_vA p N
  rw [ellA_eq_two_mul_mA_add ha ham N]
  have key : p * (2 * mA p N + (if a ≤ vA p N then 1 else 0) +
      (if p - a ≤ vA p N then 1 else 0)) = 2 * (p * mA p N) +
      p * ((if a ≤ vA p N then 1 else 0) + (if p - a ≤ vA p N then 1 else 0)) := by ring
  rw [key]
  generalize p * mA p N = q at hN ⊢
  split_ifs <;> omega

/-- **Cleared-denominator bound for `b_a`.** For `1 ≤ a ≤ m°`, `p b_a ≤ 6 N + 3 p`. -/
theorem mul_innerClassOrder_le {p a : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) (N : ℕ) :
    p * innerClassOrder p N a ≤ 6 * N + 3 * p := by
  have := mul_ellA_le ha ham N
  rw [innerClassOrder_def, mul_left_comm]
  omega

/-- **Upper bound for `b_a`.** For `1 ≤ a ≤ m°`, `b_a ≤ 6 N / p + 3`. -/
theorem innerClassOrder_le_of_le_mStar {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {p a : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) (N : ℕ) :
    (innerClassOrder p N a : α) ≤ 6 * N / p + 3 := by
  have hp : (0 : α) < p := by
    rw [mStar_def] at ham
    exact_mod_cast (by omega : 0 < p)
  rw [div_add' _ _ _ hp.ne', le_div_iff₀ hp]
  exact_mod_cast (by linarith [mul_innerClassOrder_le ha ham N] :
    innerClassOrder p N a * p ≤ 6 * N + 3 * p)

/-- **Upper bound for `b_a` in the source's parameters.** For `N = 3 n`, `K = 40 n`,
`α = 3/40` and `1 ≤ a ≤ m°`, `b_a ≤ 6 α K / p + 3`. -/
@[zeta5irr "lem_in_ba_bound"]
theorem innerClassOrder_innerDegree_le {n p a : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) :
    (innerClassOrder p (innerDegree n) a : ℚ) ≤ 6 * innerRatio * poleBound n / p + 3 := by
  rw [mul_assoc, innerRatio_mul_poleBound]
  exact innerClassOrder_le_of_le_mStar ha ham _

end Zeta5Irr
