/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.EllA
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# The inner class orders `b_a`

For a prime `p` and a residue index `1 ≤ a ≤ m°`, the inner range of the construction attaches
to the class of `a` the integer `b_a = 3 ℓ_N(a)`, where `ℓ_N(a)` counts the `j ∈ [1, N]` with
`j ≡ ±a (mod p)`. The class dimension `L_a` and the total `Z_a = L_a + b_a` are built from it.

## Main definitions

* `Zeta5Irr.innerClassOrder`: the integer `b_a = 3 ℓ_N(a)`.

## Main results

* `Zeta5Irr.innerClassOrder_neg`: `b_{-a} = b_a`.
* `Zeta5Irr.innerClassOrder_add_mul`: `b_a` depends only on `a` modulo `p`.
* `Zeta5Irr.innerClassOrder_le`: `b_a ≤ 3 N`.

## Implementation notes

* The source fixes `N = 3 n` (`Zeta5Irr.innerDegree n`); here `N` is an arbitrary natural
  number, and `p` an arbitrary natural number, since neither primality nor the value of `N`
  is needed to define `b_a`.
* The range `1 ≤ a ≤ m°` is not built into the definition: `b_a` is defined for every integer
  `a`, and the range is carried as a hypothesis by the lemmas and sums which need it.
* `b_a` is a natural number, since `ℓ_N(a)` is.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The inner class order `b_a = 3 ℓ_N(a)` attached to the residue `a` modulo `p`. -/
@[zeta5irr "def_in_ba"]
def innerClassOrder (p N : ℕ) (a : ℤ) : ℕ :=
  3 * ellA p N a

/-- Unfolding lemma for `innerClassOrder`. -/
theorem innerClassOrder_def (p N : ℕ) (a : ℤ) : innerClassOrder p N a = 3 * ellA p N a :=
  rfl

/-- The value of `b_a`, cast to any semiring. -/
@[simp, norm_cast]
theorem cast_innerClassOrder {R : Type*} [Semiring R] (p N : ℕ) (a : ℤ) :
    (innerClassOrder p N a : R) = 3 * ellA p N a := by
  simp [innerClassOrder]

/-- `b_a` is even in `a`: `b_{-a} = b_a`. -/
theorem innerClassOrder_neg (p N : ℕ) (a : ℤ) :
    innerClassOrder p N (-a) = innerClassOrder p N a := by
  simp [innerClassOrder, ellA_neg]

/-- `b_a` depends only on the residue of `a` modulo `p`. -/
theorem innerClassOrder_add_mul (p N : ℕ) (a k : ℤ) :
    innerClassOrder p N (a + p * k) = innerClassOrder p N a := by
  simp [innerClassOrder, ellA_add_mul]

/-- `b_a ≤ 3 N`. -/
theorem innerClassOrder_le (p N : ℕ) (a : ℤ) : innerClassOrder p N a ≤ 3 * N :=
  Nat.mul_le_mul_left 3 (ellA_le p N a)

/-- `b_a = 0` when `N = 0`. -/
@[simp]
theorem innerClassOrder_zero (p : ℕ) (a : ℤ) : innerClassOrder p 0 a = 0 := by
  simp [innerClassOrder]

end Zeta5Irr
