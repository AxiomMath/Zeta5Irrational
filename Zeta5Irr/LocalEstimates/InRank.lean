/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.EllA
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The rank `rk(a)` of an index in the inner range

For an odd prime `p` and `1 ≤ a ≤ m°`, the indices `1, …, m°` are ordered by decreasing value
of `ℓ_K`, ties being broken by the natural order. The rank of `a` is the number of indices
coming strictly before `a` in this order:
`rk(a) = #{1 ≤ c ≤ m° : ℓ_K(c) > ℓ_K(a)} + #{1 ≤ c < a : ℓ_K(c) = ℓ_K(a)}`.

## Main definitions

* `Zeta5Irr.inRank`: the rank `rk(a)`.

## Main results

* `Zeta5Irr.inRank_eq_card_add_card`: for `a ≤ m° + 1`, the rank is the sum of the two
  cardinalities of the source.
* `Zeta5Irr.inRank_lt_mStar`: for `1 ≤ a ≤ m°`, `rk(a) < m°`.

## Implementation notes

* The rank is defined as a single cardinality, of the set of `c ∈ [1, m°]` preceding `a` in the
  lexicographic order `ℓ_K(c) > ℓ_K(a)`, or `ℓ_K(c) = ℓ_K(a)` and `c < a`. It agrees with the
  source's sum of two cardinalities whenever `a ≤ m° + 1`, in particular on the source's
  range `1 ≤ a ≤ m°` (`inRank_eq_card_add_card`).
* The bound `K` is an arbitrary natural number rather than `40 n`, and no hypothesis is placed
  on `p` or on `a`; the source only uses the definition for an odd prime `p` and `1 ≤ a ≤ m°`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The rank `rk(a)` of an index `a` among `1, …, m°`, ordered by decreasing `ℓ_K` with ties
broken by the natural order: the number of `c ∈ [1, m°]` with `ℓ_K(c) > ℓ_K(a)`, or with
`ℓ_K(c) = ℓ_K(a)` and `c < a`. -/
@[zeta5irr "def_in_rank"]
def inRank (p K a : ℕ) : ℕ :=
  #{c ∈ Icc 1 (mStar p) | ellA p K a < ellA p K (c : ℕ) ∨ (ellA p K (c : ℕ) = ellA p K a ∧ c < a)}

/-- Unfolding lemma for `inRank`. -/
theorem inRank_def (p K a : ℕ) : inRank p K a =
    #{c ∈ Icc 1 (mStar p) |
      ellA p K a < ellA p K (c : ℕ) ∨ (ellA p K (c : ℕ) = ellA p K a ∧ c < a)} :=
  rfl

/-- For `a ≤ m° + 1` (in particular for `1 ≤ a ≤ m°`), the rank is the source's sum
`#{1 ≤ c ≤ m° : ℓ_K(c) > ℓ_K(a)} + #{1 ≤ c < a : ℓ_K(c) = ℓ_K(a)}`. -/
theorem inRank_eq_card_add_card {p K a : ℕ} (ha : a ≤ mStar p + 1) :
    inRank p K a = #{c ∈ Icc 1 (mStar p) | ellA p K a < ellA p K (c : ℕ)} +
      #{c ∈ Ico 1 a | ellA p K (c : ℕ) = ellA p K a} := by
  rw [inRank_def, filter_or, card_union_of_disjoint]
  · congr 1
    congr 1
    ext c
    simp only [mem_filter, mem_Icc, mem_Ico]
    omega
  · rw [disjoint_filter]
    intro c _ h h'
    omega

/-- For `1 ≤ a ≤ m°`, the rank satisfies `rk(a) < m°`, since `a` itself is not counted. -/
theorem inRank_lt_mStar {p K a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ mStar p) :
    inRank p K a < mStar p := by
  have hsub : ({c ∈ Icc 1 (mStar p) |
      ellA p K a < ellA p K (c : ℕ) ∨ (ellA p K (c : ℕ) = ellA p K a ∧ c < a)} : Finset ℕ) ⊂
      Icc 1 (mStar p) := by
    refine ssubset_iff_of_subset (filter_subset _ _) |>.2 ⟨a, ?_, ?_⟩
    · simp [ha₁, ha₂]
    · simp
  simpa [inRank_def] using card_lt_card hsub

end Zeta5Irr
