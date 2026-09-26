/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InE
public import Zeta5Irr.LocalEstimates.InRank
public import Zeta5Irr.LocalEstimates.InRankBij

/-!
# The extras indicator `ε_a`

For an odd prime `p`, an integer `M ≥ 40` and `1 ≤ a ≤ m°`, the `E` extra dimensions of the
inner range are given to the first `E` square classes in decreasing order of `ℓ_K`, ties being
broken by the natural order. The indicator of this choice is
`ε_a = 1` if `rk(a) < E` and `ε_a = 0` if `rk(a) ≥ E`.

## Main definitions

* `Zeta5Irr.extraIndicator`: the indicator `ε_a`.

## Main results

* `Zeta5Irr.extraIndicator_eq_one_iff`, `Zeta5Irr.extraIndicator_eq_zero_iff`: `ε_a = 1` iff
  `rk(a) < E`, and `ε_a = 0` iff `E ≤ rk(a)`.
* `Zeta5Irr.extraIndicator_le_one`: `ε_a ≤ 1`.
* `Zeta5Irr.sum_extraIndicator`: if `0 ≤ E ≤ m°` then `∑_{1 ≤ a ≤ m°} ε_a = E`.

## Implementation notes

* The indicator is natural-number valued, so that it can be summed and multiplied into
  integer bounds. Since `E` is an integer, the comparison `rk(a) < E` is made in `ℤ`.
* The integers `K = 40 n`, `h = 37 n` and `N = 3 n` are functions of `n`, so `ε_a` takes `n`
  as an argument along with `p`, `M` and `a`. The hypotheses that `p` is an odd prime,
  `M ≥ 40` and `1 ≤ a ≤ m°` are not needed to define `ε_a`; they are carried by the lemmas
  which use them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The extras indicator `ε_a`: equal to `1` if the rank `rk(a)` (for the pole bound
`K = 40 n`) is less than the number of extras `E`, and to `0` otherwise. -/
@[zeta5irr "def_in_eps"]
def extraIndicator (n p M a : ℕ) : ℕ :=
  if (inRank p (poleBound n) a : ℤ) < extraCount n p M then 1 else 0

/-- Unfolding lemma for `extraIndicator`. -/
theorem extraIndicator_def (n p M a : ℕ) : extraIndicator n p M a =
    if (inRank p (poleBound n) a : ℤ) < extraCount n p M then 1 else 0 :=
  rfl

/-- `ε_a = 1` if and only if `rk(a) < E`. -/
theorem extraIndicator_eq_one_iff {n p M a : ℕ} :
    extraIndicator n p M a = 1 ↔ (inRank p (poleBound n) a : ℤ) < extraCount n p M := by
  rw [extraIndicator_def]
  split_ifs with h <;> simp [h]

/-- `ε_a = 0` if and only if `E ≤ rk(a)`. -/
theorem extraIndicator_eq_zero_iff {n p M a : ℕ} :
    extraIndicator n p M a = 0 ↔ extraCount n p M ≤ (inRank p (poleBound n) a : ℤ) := by
  rw [extraIndicator_def]
  split_ifs with h <;> simp [h, not_lt.mp]

/-- `ε_a ≤ 1`. -/
theorem extraIndicator_le_one (n p M a : ℕ) : extraIndicator n p M a ≤ 1 := by
  rw [extraIndicator_def]
  split_ifs <;> simp

/-- If `0 ≤ E ≤ m°`, then exactly `E` of the indices `1 ≤ a ≤ m°` receive an extra:
`∑_{1 ≤ a ≤ m°} ε_a = E`. -/
theorem sum_extraIndicator {n p M : ℕ} (h₀ : 0 ≤ extraCount n p M)
    (h₁ : extraCount n p M ≤ mStar p) :
    ((∑ a ∈ Icc 1 (mStar p), extraIndicator n p M a : ℕ) : ℤ) = extraCount n p M := by
  set E := extraCount n p M
  set f := inRank p (poleBound n)
  have hbij := bijOn_inRank p (poleBound n)
  have himage : (Icc 1 (mStar p)).image f = range (mStar p) := by
    rw [← coe_inj, coe_image]
    exact hbij.image_eq
  have hsum : ∑ a ∈ Icc 1 (mStar p), extraIndicator n p M a =
      #{a ∈ Icc 1 (mStar p) | (f a : ℤ) < E} := by
    simp only [extraIndicator_def, card_filter, f, E]
  have hcard : #{a ∈ Icc 1 (mStar p) | (f a : ℤ) < E} =
      #{r ∈ range (mStar p) | ((r : ℕ) : ℤ) < E} := by
    rw [← himage, filter_image, card_image_of_injOn]
    exact hbij.injOn.mono (coe_subset.mpr (filter_subset _ _))
  have hrange : ({r ∈ range (mStar p) | ((r : ℕ) : ℤ) < E} : Finset ℕ) = range E.toNat := by
    ext r
    simp only [mem_filter, mem_range]
    omega
  rw [hsum, hcard, hrange, card_range, Int.toNat_of_nonneg h₀]

end Zeta5Irr
