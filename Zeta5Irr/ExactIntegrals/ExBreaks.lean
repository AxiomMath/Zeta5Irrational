/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The breakpoints of the partition of `[3, 20]`

The integrands of the exact integrals involve `⌊γ x⌋` for finitely many slopes `γ`, and such a
floor is constant on every open interval free of the points `k / γ` with `k ∈ ℤ`. The partition
of `[3, 20]` used to evaluate these integrals therefore has as breakpoints the endpoints `3` and
`20` together with all points `k / γ ∈ (3, 20)`, for the seven slopes
`γ ∈ {2, 2α, 2λ, 2H, 4α, 2(1 - α), 2(1 + α)}`:
`𝓔 = {3, 20} ∪ ⋃_γ {k / γ : k ∈ ℤ, 3γ < k < 20γ}`.

We first define, for arbitrary rationals `a, b` and a finite set of slopes, the finite set of
such breakpoints, and characterise its elements; `𝓔` is then its value at `a = 3`, `b = 20`.

## Main definitions

* `Zeta5Irr.breakpoints`: the set `{a, b} ∪ ⋃_{γ ∈ Γ} {k / γ : k ∈ ℤ, a γ < k < b γ}`.
* `Zeta5Irr.breakSlopes`: the seven slopes `2, 2α, 2λ, 2H, 4α, 2(1 - α), 2(1 + α)`.
* `Zeta5Irr.exBreaks`: the breakpoint set `𝓔` of the partition of `[3, 20]`.

## Main results

* `Zeta5Irr.mem_breakpoints`: `x ∈ breakpoints a b Γ` iff `x = a`, `x = b`, or `x = k / γ` for
  some `γ ∈ Γ` and some integer `k` with `a γ < k < b γ`.
* `Zeta5Irr.mem_exBreaks`: the same characterisation for `𝓔`, which is the source's definition.
* `Zeta5Irr.card_exBreaks`: `𝓔` has `144` elements.

## Implementation notes

* The set is a `Finset ℚ`, so that its cardinality, its elements and their order are
  computable. For each slope the integers `k` with `a γ < k < b γ` are those of the open integer
  interval `(⌊a γ⌋, ⌈b γ⌉)`; this holds for every rational `γ`, with no sign condition.
* The slopes `2λ` and `2(1 - α)` coincide, since `λ = 1 - α`; the source lists both, and so does
  `breakSlopes`, which as a `Finset` has six elements.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.2: the partition of `[3, 20]`.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The breakpoints `{a, b} ∪ ⋃_{γ ∈ Γ} {k / γ : k ∈ ℤ, a γ < k < b γ}` determined by the
endpoints `a, b` and a finite set `Γ` of slopes: the points of `(a, b)` at which one of the
functions `x ↦ ⌊γ x⌋` may jump, together with the endpoints. -/
def breakpoints (a b : ℚ) (Γ : Finset ℚ) : Finset ℚ :=
  {a, b} ∪ Γ.biUnion fun γ => (Ioo ⌊a * γ⌋ ⌈b * γ⌉).image fun k : ℤ => (k : ℚ) / γ

/-- `x ∈ breakpoints a b Γ` iff `x = a`, `x = b`, or `x = k / γ` for some `γ ∈ Γ` and some
integer `k` with `a γ < k < b γ`. -/
theorem mem_breakpoints {a b x : ℚ} {Γ : Finset ℚ} :
    x ∈ breakpoints a b Γ ↔
      x = a ∨ x = b ∨ ∃ γ ∈ Γ, ∃ k : ℤ, a * γ < k ∧ (k : ℚ) < b * γ ∧ x = k / γ := by
  simp only [breakpoints, mem_union, mem_insert, mem_singleton, mem_biUnion, mem_image,
    mem_Ioo, Int.floor_lt, Int.lt_ceil, or_assoc]
  refine or_congr_right (or_congr_right ?_)
  constructor
  · rintro ⟨γ, hγ, k, ⟨h1, h2⟩, rfl⟩
    exact ⟨γ, hγ, k, h1, h2, rfl⟩
  · rintro ⟨γ, hγ, k, h1, h2, rfl⟩
    exact ⟨γ, hγ, k, ⟨h1, h2⟩, rfl⟩

/-- The left endpoint `a` is a breakpoint. -/
theorem left_mem_breakpoints (a b : ℚ) (Γ : Finset ℚ) : a ∈ breakpoints a b Γ :=
  mem_breakpoints.2 (Or.inl rfl)

/-- The right endpoint `b` is a breakpoint. -/
theorem right_mem_breakpoints (a b : ℚ) (Γ : Finset ℚ) : b ∈ breakpoints a b Γ :=
  mem_breakpoints.2 (Or.inr (Or.inl rfl))

/-- If every slope is positive and `a ≤ b`, every breakpoint lies in `[a, b]`. -/
theorem mem_Icc_of_mem_breakpoints {a b x : ℚ} {Γ : Finset ℚ} (hab : a ≤ b)
    (hΓ : ∀ γ ∈ Γ, 0 < γ) (hx : x ∈ breakpoints a b Γ) : x ∈ Set.Icc a b := by
  rcases mem_breakpoints.1 hx with rfl | rfl | ⟨γ, hγ, k, h1, h2, rfl⟩
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩
  · have := hΓ γ hγ
    exact ⟨(le_div_iff₀ this).2 h1.le, (div_le_iff₀ this).2 h2.le⟩

/-- The seven slopes `2, 2α, 2λ, 2H, 4α, 2(1 - α), 2(1 + α)` whose floors the exact integrals
involve, where `α = 3/40`, `λ = 37/40` and `H = 23/20`. -/
def breakSlopes : Finset ℚ :=
  {2, 2 * innerRatio, 2 * orderRatio, 2 * heightRatio, 4 * innerRatio, 2 * (1 - innerRatio),
    2 * (1 + innerRatio)}

/-- Each of the slopes in `breakSlopes` is positive. -/
theorem breakSlopes_pos {γ : ℚ} (hγ : γ ∈ breakSlopes) : 0 < γ := by
  simp only [breakSlopes, innerRatio, orderRatio, heightRatio, mem_insert, mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The breakpoint set `𝓔 = {3, 20} ∪ ⋃_γ {k / γ : k ∈ ℤ, 3γ < k < 20γ}` of the partition of
`[3, 20]`, the union running over `γ ∈ {2, 2α, 2λ, 2H, 4α, 2(1 - α), 2(1 + α)}`. -/
@[zeta5irr "def_ex_breaks"]
def exBreaks : Finset ℚ :=
  breakpoints 3 20 breakSlopes

/-- The source's definition of `𝓔`: `x ∈ 𝓔` iff `x ∈ {3, 20}` or `x = k / γ` for one of the
seven slopes `γ` and an integer `k` with `3γ < k < 20γ`. -/
@[zeta5irr "def_ex_breaks"]
theorem mem_exBreaks {x : ℚ} :
    x ∈ exBreaks ↔ x = 3 ∨ x = 20 ∨
      ∃ γ ∈ ({2, 2 * innerRatio, 2 * orderRatio, 2 * heightRatio, 4 * innerRatio,
          2 * (1 - innerRatio), 2 * (1 + innerRatio)} : Finset ℚ),
        ∃ k : ℤ, 3 * γ < k ∧ (k : ℚ) < 20 * γ ∧ x = k / γ :=
  mem_breakpoints

/-- Every point of `𝓔` lies in `[3, 20]`. -/
theorem mem_Icc_of_mem_exBreaks {x : ℚ} (hx : x ∈ exBreaks) : x ∈ Set.Icc (3 : ℚ) 20 :=
  mem_Icc_of_mem_breakpoints (by norm_num) (fun _ => breakSlopes_pos) hx

/-- The partition of `[3, 20]` has `144` breakpoints. -/
@[zeta5irr "lem_ex_card"]
theorem card_exBreaks : exBreaks.card = 144 := by
  decide +kernel

end Zeta5Irr
