/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.EllA
public import Zeta5Irr.LimitingFunctions.Qx

/-!
# The number of large classes `𝒜_p(K)`

For a prime `p` and an integer `K`, the number of large classes is
`𝒜_p(K) = #{a ∈ ℤ : 1 ≤ a ≤ m°, ℓ_K(a) = q̃(K/p) + 1}`,
where `m° = (p - 1) / 2`, `ℓ_K(a)` counts the `j ∈ [1, K]` with `j ≡ ±a (mod p)`, and
`q̃(x) = ⌊2 x⌋`. It counts the nonzero square classes which receive one more pole than the
base count `q̃(K/p)`.

## Main definitions

* `Zeta5Irr.largeClassCount`: the number of large classes `𝒜_p(K)`.

## Main results

* `Zeta5Irr.mem_largeClasses`: membership in the set of large classes.
* `Zeta5Irr.largeClassCount_le_mStar`: `𝒜_p(K) ≤ m°`.
* `Zeta5Irr.largeClassCount_eq_card_nat`: the condition
  `ℓ_K(a) = q̃(K/p) + 1` is the natural-number equation `ℓ_K(a) = ⌊2K/p⌋ + 1`.

## Implementation notes

* The source fixes an integer `M ≥ 40`, an integer `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²` and a
  prime `p` with `K/M < p ≤ K/3`. None of these hypotheses is needed to state the count, so
  `largeClassCount` is defined for all natural numbers `K` and `p`; the hypotheses are carried
  by the results that use it.
* The index `a` ranges over `Finset.Icc 1 m° ⊆ ℕ`, cast to `ℤ` for `ℓ_K`, and the count is a
  `Finset.card`, so that it can be used in exact summation identities.
* The condition compares the natural number `ℓ_K(a)` with the real number `q̃(K/p) + 1`, as
  in the source; `largeClassCount_eq_card_nat` rewrites it as an equation in `ℕ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3: the inner asymptotics.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The set of large classes: the `a ∈ [1, m°]` with `ℓ_K(a) = q̃(K/p) + 1`. -/
noncomputable def largeClasses (K p : ℕ) : Finset ℕ :=
  {a ∈ Icc 1 (mStar p) | (ellA p K a : ℝ) = basePoleCount ((K : ℝ) / p) + 1}

/-- **The number of large classes.**
`𝒜_p(K) = #{a ∈ ℤ : 1 ≤ a ≤ m°, ℓ_K(a) = q̃(K/p) + 1}`. -/
@[zeta5irr "def_norm_extracount"]
noncomputable def largeClassCount (K p : ℕ) : ℕ := #(largeClasses K p)

/-- Unfolding lemma for `largeClassCount`. -/
theorem largeClassCount_def (K p : ℕ) : largeClassCount K p = #(largeClasses K p) := rfl

/-- Membership in the set of large classes. -/
theorem mem_largeClasses {K p a : ℕ} :
    a ∈ largeClasses K p ↔
      1 ≤ a ∧ a ≤ mStar p ∧ (ellA p K a : ℝ) = basePoleCount ((K : ℝ) / p) + 1 := by
  simp [largeClasses, and_assoc]

/-- The large classes lie in `[1, m°]`. -/
theorem largeClasses_subset (K p : ℕ) : largeClasses K p ⊆ Icc 1 (mStar p) :=
  filter_subset _ _

/-- `𝒜_p(K) ≤ m°`. -/
theorem largeClassCount_le_mStar (K p : ℕ) : largeClassCount K p ≤ mStar p :=
  (card_le_card (largeClasses_subset K p)).trans (by simp)

/-- `q̃(K/p) = ⌊2K/p⌋` is the natural-number quotient `2K / p`. -/
theorem basePoleCount_natCast_div (K p : ℕ) :
    basePoleCount ((K : ℝ) / p) = ((2 * K / p : ℕ) : ℝ) := by
  rw [basePoleCount_def, ← mul_div_assoc,
    show (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) by push_cast; ring, Int.floor_div_natCast,
    Int.floor_natCast]
  norm_cast

/-- The large classes are the `a ∈ [1, m°]` with `ℓ_K(a) = ⌊2K/p⌋ + 1`, an
equation in `ℕ`. -/
theorem largeClasses_eq_filter_nat (K p : ℕ) :
    largeClasses K p =
      (Icc 1 (mStar p)).filter (fun a : ℕ => ellA p K a = 2 * K / p + 1) := by
  unfold largeClasses
  congr 1
  ext a
  rw [basePoleCount_natCast_div]
  exact_mod_cast Iff.rfl

/-- `𝒜_p(K) = #{a ∈ [1, m°] : ℓ_K(a) = ⌊2K/p⌋ + 1}`, counted in `ℕ`. -/
theorem largeClassCount_eq_card_nat (K p : ℕ) :
    largeClassCount K p =
      #((Icc 1 (mStar p)).filter (fun a : ℕ => ellA p K a = 2 * K / p + 1)) := by
  rw [largeClassCount_def, largeClasses_eq_filter_nat]

end Zeta5Irr
