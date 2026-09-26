/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InRank

/-!
# The rank map is a bijection onto `{0, …, m° - 1}`

The indices `1, …, m°` are totally ordered by `c ≺ a` when `ℓ_K(c) > ℓ_K(a)`, or
`ℓ_K(c) = ℓ_K(a)` and `c < a`, and the rank `rk(a)` counts the indices preceding `a`. The rank
is strictly increasing for `≺`, hence injective, and takes values below `m°`; an injective map
between two finite sets of the same size `m°` is a bijection.

## Main results

* `Zeta5Irr.inRank_lt_inRank`: if `c ≺ a` then `rk(c) < rk(a)`.
* `Zeta5Irr.injOn_inRank`: `rk` is injective on `{1, …, m°}`.
* `Zeta5Irr.bijOn_inRank`: `rk` is a bijection from `{1, …, m°}` onto `{0, …, m° - 1}`.

## Implementation notes

* The source assumes `p` is an odd prime; the statement holds for every natural number `p`
  (with `m° = (p - 1) / 2`) and every bound `K`, and is stated so.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3 (The inner range: dimensions).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- If `c` precedes `a` in the order by decreasing `ℓ_K` with ties broken by the natural order,
and `c ∈ [1, m°]`, then `rk(c) < rk(a)`. -/
theorem inRank_lt_inRank {p K a c : ℕ} (hc : c ∈ Icc 1 (mStar p))
    (h : ellA p K a < ellA p K (c : ℕ) ∨ (ellA p K (c : ℕ) = ellA p K a ∧ c < a)) :
    inRank p K c < inRank p K a := by
  rw [inRank_def, inRank_def]
  refine card_lt_card <| (ssubset_iff_of_subset ?_).2 ⟨c, ?_, ?_⟩
  · intro d hd
    simp only [mem_filter] at hd ⊢
    refine ⟨hd.1, ?_⟩
    omega
  · simp only [mem_filter]
    exact ⟨hc, h⟩
  · simp

/-- The rank `rk` is injective on `{1, …, m°}`. -/
theorem injOn_inRank (p K : ℕ) : Set.InjOn (inRank p K) (Icc 1 (mStar p) : Set ℕ) := by
  intro a ha c hc hac
  by_contra hne
  rcases lt_trichotomy (ellA p K a) (ellA p K (c : ℕ)) with h | h | h
  · exact (inRank_lt_inRank hc (Or.inl h)).ne' hac
  · rcases lt_or_gt_of_ne hne with h' | h'
    · exact (inRank_lt_inRank ha (Or.inr ⟨h, h'⟩)).ne hac
    · exact (inRank_lt_inRank hc (Or.inr ⟨h.symm, h'⟩)).ne' hac
  · exact (inRank_lt_inRank ha (Or.inl h)).ne hac

/-- **The rank is a bijection.** The map `a ↦ rk(a)` is a bijection from `{1, …, m°}` onto
`{0, 1, …, m° - 1}`. -/
@[zeta5irr "lem_in_rank_bij"]
theorem bijOn_inRank (p K : ℕ) :
    Set.BijOn (inRank p K) (Icc 1 (mStar p) : Set ℕ) (range (mStar p) : Set ℕ) := by
  have hmaps : Set.MapsTo (inRank p K) (Icc 1 (mStar p) : Set ℕ) (range (mStar p) : Set ℕ) := by
    intro a ha
    simp only [coe_Icc, Set.mem_Icc, coe_range, Set.mem_Iio] at ha ⊢
    exact inRank_lt_mStar ha.1 ha.2
  refine ⟨hmaps, injOn_inRank p K, ?_⟩
  intro b hb
  obtain ⟨a, ha, hab⟩ := surj_on_of_inj_on_of_card_le (s := Icc 1 (mStar p))
    (t := range (mStar p)) (fun a ha => inRank p K a) (fun a ha => hmaps ha)
    (fun a c ha hc h => injOn_inRank p K ha hc h) (by simp) b hb
  exact ⟨a, ha, hab.symm⟩

end Zeta5Irr
