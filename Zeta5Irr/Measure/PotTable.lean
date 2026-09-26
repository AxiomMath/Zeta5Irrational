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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The refinement table `𝒯`

The interval bound on `[0, 2]` is verified on a finite family of dyadic intervals
`[k / 2^d, (k + 1) / 2^d]`, each attached to a grid index `j`. The refinement table `𝒯` is the
explicit finite set of triples `(j, d, k)` that lists them. It is given in the source as a table
of rows `(j, d, K)`, where `K` is a range `a, …, b` of values of `k` (endpoints included) or the
union of two such ranges; it has `684` members.

## Main definitions

* `Zeta5Irr.potTableBlocks`: the rows of the table, one quadruple `(j, d, a, b)` for each range
  `a, …, b` of values of `k`.
* `Zeta5Irr.potTable`: the refinement table `𝒯`, a finite set of triples `(j, d, k)`.

## Main results

* `Zeta5Irr.mem_potTable`: `(j, d, k) ∈ 𝒯` if and only if some row `(j, d, a, b)` has
  `a ≤ k ≤ b`.
* `Zeta5Irr.potTableBlocks_separated`: distinct rows with the same `(j, d)` have disjoint
  ranges of `k`.
* `Zeta5Irr.card_potTable`: `𝒯` has `684` members.

## Implementation notes

* All entries of the table are nonnegative, so `𝒯` is a `Finset (ℕ × ℕ × ℕ)`; its members are
  cast to `ℝ` wherever the interval `[k / 2^d, (k + 1) / 2^d]` is formed.
* A row of the source whose last column is the union of two ranges is split into two
  consecutive entries of `Zeta5Irr.potTableBlocks` with the same `(j, d)`.
* Membership in `𝒯` is decidable, so statements quantified over `𝒯` can be checked by
  enumeration.
* The count `684` is obtained as the sum of the lengths `b - a + 1` of the rows, which is
  legitimate because the rows are pairwise disjoint; the separation of the rows is decided on
  the list of `116` rows rather than on the `684` triples.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6: the interval bound and the partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr

/-- The rows of the refinement table: a quadruple `(j, d, a, b)` stands for the triples
`(j, d, k)` with `a ≤ k ≤ b`. A row of the source table listing two ranges of `k` appears here
as two consecutive quadruples. -/
def potTableBlocks : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 1, 0, 0), (0, 2, 2, 3),
   (1, 0, 0, 0), (2, 0, 0, 0), (3, 0, 0, 0), (4, 0, 0, 0),
   (5, 0, 0, 0), (6, 0, 0, 0), (7, 0, 0, 0), (8, 0, 0, 0),
   (9, 1, 0, 1), (10, 1, 0, 1), (11, 1, 0, 1),
   (12, 1, 0, 0), (12, 2, 2, 3),
   (13, 2, 0, 3), (14, 2, 0, 3),
   (15, 1, 0, 0), (15, 2, 2, 3),
   (16, 0, 0, 0), (17, 0, 0, 0), (18, 0, 0, 0),
   (19, 1, 1, 1), (19, 3, 0, 0), (19, 3, 2, 3), (19, 4, 2, 3),
   (20, 2, 3, 3), (20, 3, 4, 5), (20, 4, 0, 1), (20, 4, 6, 7), (20, 5, 4, 11),
   (21, 2, 3, 3), (21, 3, 5, 5), (21, 4, 0, 0), (21, 4, 7, 9), (21, 5, 2, 4),
   (21, 5, 10, 13), (21, 6, 10, 19),
   (22, 3, 5, 7), (22, 4, 0, 0), (22, 4, 8, 9), (22, 5, 2, 3), (22, 5, 12, 15),
   (22, 6, 8, 23),
   (23, 3, 6, 7), (23, 4, 9, 11), (23, 5, 0, 2), (23, 5, 14, 17), (23, 6, 6, 13),
   (23, 6, 19, 27), (23, 7, 28, 37),
   (24, 3, 6, 7), (24, 4, 10, 11), (24, 5, 0, 2), (24, 5, 15, 19), (24, 6, 6, 11),
   (24, 6, 22, 29), (24, 7, 24, 43),
   (25, 3, 7, 7), (25, 4, 10, 13), (25, 5, 0, 2), (25, 5, 16, 19), (25, 6, 6, 11),
   (25, 6, 24, 31), (25, 7, 24, 47),
   (26, 3, 7, 7), (26, 4, 11, 13), (26, 5, 0, 2), (26, 5, 17, 21), (26, 6, 6, 11),
   (26, 6, 25, 33), (26, 7, 24, 49),
   (27, 4, 11, 15), (27, 5, 0, 2), (27, 5, 17, 21), (27, 6, 6, 11), (27, 6, 26, 33),
   (27, 7, 24, 51),
   (28, 4, 12, 15), (28, 5, 0, 2), (28, 5, 18, 23), (28, 6, 6, 11), (28, 6, 27, 35),
   (28, 7, 24, 53),
   (29, 4, 13, 15), (29, 5, 0, 2), (29, 5, 19, 25), (29, 6, 6, 12), (29, 6, 27, 37),
   (29, 7, 26, 53),
   (30, 4, 13, 15), (30, 5, 0, 2), (30, 5, 20, 25), (30, 6, 6, 14), (30, 6, 26, 39),
   (30, 7, 30, 51),
   (31, 4, 14, 15), (31, 5, 0, 2), (31, 5, 20, 27), (31, 6, 6, 39),
   (32, 4, 15, 15), (32, 5, 0, 4), (32, 5, 19, 29), (32, 6, 10, 37),
   (33, 4, 0, 0), (33, 4, 15, 15), (33, 5, 2, 29),
   (34, 2, 2, 3), (34, 3, 3, 3), (34, 4, 3, 5), (34, 5, 4, 5), (34, 6, 5, 7),
   (34, 7, 6, 9), (34, 8, 7, 11), (34, 9, 5, 13), (34, 10, 0, 9)]

/-- The refinement table `𝒯`: the set of triples `(j, d, k)` with `a ≤ k ≤ b` for some row
`(j, d, a, b)` of `Zeta5Irr.potTableBlocks`. -/
@[zeta5irr "def_pot_table"]
def potTable : Finset (ℕ × ℕ × ℕ) :=
  potTableBlocks.toFinset.biUnion fun B => {B.1} ×ˢ {B.2.1} ×ˢ Finset.Icc B.2.2.1 B.2.2.2

/-- A triple `(j, d, k)` lies in the refinement table if and only if some row `(j, d, a, b)` of
the table has `a ≤ k ≤ b`. -/
theorem mem_potTable {j d k : ℕ} :
    (j, d, k) ∈ potTable ↔ ∃ a b, (j, d, a, b) ∈ potTableBlocks ∧ a ≤ k ∧ k ≤ b := by
  simp only [potTable, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨j', d', a, b⟩, hB, rfl, rfl, hk⟩
    exact ⟨a, b, hB, hk⟩
  · rintro ⟨a, b, hB, hk⟩
    exact ⟨(j, d, a, b), hB, rfl, rfl, hk⟩

/-- Two distinct rows of the refinement table either differ in `(j, d)` or have disjoint ranges
of `k`. -/
theorem potTableBlocks_separated :
    ∀ B ∈ potTableBlocks, ∀ C ∈ potTableBlocks, B ≠ C →
      B.1 ≠ C.1 ∨ B.2.1 ≠ C.2.1 ∨ B.2.2.2 < C.2.2.1 ∨ C.2.2.2 < B.2.2.1 := by
  decide +kernel

/-- The refinement table has `684` members. -/
theorem card_potTable : potTable.card = 684 := by
  rw [potTable, Finset.card_biUnion]
  · rw [List.sum_toFinset _ (by decide +kernel)]
    simp [potTableBlocks]
  · intro B hB C hC hBC
    rw [Finset.mem_coe, List.mem_toFinset] at hB hC
    obtain ⟨j, d, a, b⟩ := B
    obtain ⟨j', d', a', b'⟩ := C
    have h := potTableBlocks_separated _ hB _ hC hBC
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_Icc]
    rintro ⟨x, y, z⟩ ⟨rfl, rfl, h₁, h₂⟩ ⟨rfl, rfl, h₃, h₄⟩
    simp only [ne_eq, not_true_eq_false, false_or] at h
    omega

end Zeta5Irr
