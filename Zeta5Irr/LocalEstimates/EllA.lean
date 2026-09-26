/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The counting function `ℓ_A`

For a modulus `p`, a bound `A ≥ 0` and an integer `a`, the number `ℓ_A(a)` counts the integers
`j` with `1 ≤ j ≤ A` which are congruent to `a` or to `-a` modulo `p`:
`ℓ_A(a) = #{j ∈ ℤ : 1 ≤ j ≤ A, j ≡ a or j ≡ -a (mod p)}`.

## Main definitions

* `Zeta5Irr.ellA`: the counting function `ℓ_A(a)`.

## Main results

* `Zeta5Irr.ellA_neg`: `ℓ_A(-a) = ℓ_A(a)`.
* `Zeta5Irr.ellA_add_mul`: `ℓ_A` depends only on `a` modulo `p`.
* `Zeta5Irr.ellA_le`: `ℓ_A(a) ≤ A`.
* `Zeta5Irr.ellA_zero`: `ℓ_0(a) = 0`.
* `Zeta5Irr.card_filter_Ioc_intCast`: counting `N < j ≤ K` with `j ≡ ±a (mod p)` over `ℤ` or
  over `ℕ` (with the congruence in `ZMod p`) gives the same number.
* `Zeta5Irr.ellA_eq_card_filter_nat`: `ℓ_A(a)` counted over `1 ≤ j ≤ A` in `ℕ`, with the
  congruence in `ZMod p`.

## Implementation notes

* The source takes `p` prime; primality is not needed to define `ℓ_A`, so `p` is an arbitrary
  natural number here.
* Since only `A ≥ 0` occurs, `A` is a natural number; `j` ranges over the integers
  `Finset.Icc 1 A ⊆ ℤ` (with `A` cast to `ℤ`). The count over `1 ≤ j ≤ A` in `ℕ` is
  `ellA_eq_card_filter_nat`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The counting function `ℓ_A(a) = #{j : 1 ≤ j ≤ A, j ≡ ±a (mod p)}`. -/
@[zeta5irr "def_ellA"]
def ellA (p A : ℕ) (a : ℤ) : ℕ :=
  #{j ∈ Icc 1 A | (j : ℤ) ≡ a [ZMOD p] ∨ (j : ℤ) ≡ -a [ZMOD p]}

/-- `ℓ_A` is even: `ℓ_A(-a) = ℓ_A(a)`. -/
theorem ellA_neg (p A : ℕ) (a : ℤ) : ellA p A (-a) = ellA p A a := by
  unfold ellA
  congr 1
  ext j
  simp only [neg_neg, mem_filter, or_comm]

/-- `ℓ_A(a)` depends only on the residue of `a` modulo `p`. -/
theorem ellA_add_mul (p A : ℕ) (a k : ℤ) : ellA p A (a + p * k) = ellA p A a := by
  unfold ellA
  congr 1
  ext j
  have h₁ : a + p * k ≡ a [ZMOD p] := Int.modEq_add_fac_self
  have h₂ : -(a + p * k) ≡ -a [ZMOD p] := h₁.neg
  simp only [mem_filter]
  constructor
  · rintro ⟨hj, h | h⟩
    exacts [⟨hj, .inl (h.trans h₁)⟩, ⟨hj, .inr (h.trans h₂)⟩]
  · rintro ⟨hj, h | h⟩
    exacts [⟨hj, .inl (h.trans h₁.symm)⟩, ⟨hj, .inr (h.trans h₂.symm)⟩]

/-- `ℓ_A(a)` is at most `A`. -/
theorem ellA_le (p A : ℕ) (a : ℤ) : ellA p A a ≤ A :=
  (card_filter_le _ _).trans (by simp)

/-- `ℓ_0(a) = 0`. -/
@[simp]
theorem ellA_zero (p : ℕ) (a : ℤ) : ellA p 0 a = 0 := by
  simp [ellA]

/-- `ℓ_A(a)` counts the integers `j ∈ (0, A]` with `j ≡ ±a (mod p)`. -/
theorem ellA_eq_card_filter_Ioc (p A : ℕ) (a : ℤ) :
    ellA p A a = #{j ∈ Ioc (0 : ℤ) A | j ≡ a [ZMOD p] ∨ j ≡ -a [ZMOD p]} := by
  unfold ellA
  congr 2
  ext j
  simp only [mem_Icc, mem_Ioc]
  omega

/-- For a natural number `j`, the congruence `j ≡ ±a (mod p)` holds in `ZMod p` iff it holds as
a congruence of integers. -/
theorem natCast_eq_or_eq_neg_iff_intModEq (p : ℕ) (a : ℤ) (j : ℕ) :
    ((j : ZMod p) = a ∨ (j : ZMod p) = -a) ↔ ((j : ℤ) ≡ a [ZMOD p] ∨ (j : ℤ) ≡ -a [ZMOD p]) := by
  rw [← Int.cast_natCast (R := ZMod p), ← Int.cast_neg, ZMod.intCast_eq_intCast_iff,
    ZMod.intCast_eq_intCast_iff]

/-- The integers `N < j ≤ K` with `j ≡ ±a (mod p)` and the natural numbers `N < j ≤ K` with
`j ≡ ±a` in `ZMod p` are equinumerous. -/
theorem card_filter_Ioc_intCast (p N K : ℕ) (a : ℤ) :
    #{j ∈ Ioc (N : ℤ) K | j ≡ a [ZMOD p] ∨ j ≡ -a [ZMOD p]} =
      #((Ioc N K).filter fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a) := by
  symm
  refine card_nbij' (fun j : ℕ ↦ (j : ℤ)) (fun j : ℤ ↦ j.toNat) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Ioc] at hj ⊢
    exact ⟨by omega, (natCast_eq_or_eq_neg_iff_intModEq p a j).mp hj.2⟩
  · intro j hj
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Ioc] at hj ⊢
    have hj0 : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
    exact ⟨by omega, (natCast_eq_or_eq_neg_iff_intModEq p a _).mpr (hj0 ▸ hj.2)⟩
  · exact fun j _ ↦ by simp
  · intro j hj
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Ioc] at hj
    exact Int.toNat_of_nonneg (by omega)

/-- `ℓ_A(a)` counted over the natural numbers `1 ≤ j ≤ A`, with the congruence in `ZMod p`. -/
theorem ellA_eq_card_filter_nat (p A : ℕ) (a : ℤ) :
    ellA p A a = #((Icc 1 A).filter fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a) := by
  rw [ellA_eq_card_filter_Ioc, ← Nat.cast_zero, card_filter_Ioc_intCast]
  rfl

end Zeta5Irr
