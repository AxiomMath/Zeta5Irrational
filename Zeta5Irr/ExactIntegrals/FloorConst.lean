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
# The floor of `β x` is constant between consecutive lattice points

Let `l < r` be real numbers such that `β x` is never an integer for `l < x < r`. Then
`⌊β x⌋` is constant on the open interval `(l, r)`. The reason is the intermediate value theorem:
if `⌊β x⌋ < ⌊β x'⌋` then the integer `k = ⌊β x⌋ + 1` satisfies `β x < k ≤ β x'`, so `β y = k`
for some `y` between `x` and `x'`.

The argument uses nothing about `y ↦ β y` beyond continuity and nothing about `(l, r)` beyond
connectedness, and we prove it in that generality first.

## Main results

* `Zeta5Irr.floor_eq_floor_of_isPreconnected`: if `f` is continuous on a preconnected set `s`
  and takes no integer value on `s`, then `⌊f x⌋ = ⌊f x'⌋` for all `x, x' ∈ s`.
* `Zeta5Irr.floor_mul_eq_floor_mul_of_mem_Ioo`: if `β y ∉ ℤ` for all `y ∈ (l, r)`, then
  `⌊β x⌋ = ⌊β x'⌋` for all `x, x' ∈ (l, r)`.

## Implementation notes

The source assumes `β > 0` and `l < r`. Neither is needed: for `β ≤ 0` the map `y ↦ β y` is
still continuous, and for `l ≥ r` the interval is empty and the statement is vacuous.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §6 (the inner integral).
-/

@[expose] public section

namespace Zeta5Irr

open Set

/-- If `f` is continuous on a preconnected set `s` and `f y` is never an integer for `y ∈ s`,
then `⌊f⌋` is constant on `s`. -/
theorem floor_eq_floor_of_isPreconnected {s : Set ℝ} {f : ℝ → ℝ} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (hint : ∀ y ∈ s, ∀ k : ℤ, f y ≠ k) {x x' : ℝ} (hx : x ∈ s)
    (hx' : x' ∈ s) : ⌊f x⌋ = ⌊f x'⌋ := by
  have hc : (f '' s).OrdConnected := (hs.image f hf).ordConnected
  wlog h : ⌊f x⌋ < ⌊f x'⌋ generalizing x x'
  · rcases (not_lt.1 h).lt_or_eq with h | h
    · exact (this hx' hx h).symm
    · exact h.symm
  exfalso
  have h1 : f x < (⌊f x⌋ + 1 : ℤ) := by push_cast; exact Int.lt_floor_add_one _
  have h2 : ((⌊f x⌋ + 1 : ℤ) : ℝ) ≤ f x' :=
    (Int.cast_le.2 (Int.add_one_le_iff.2 h)).trans (Int.floor_le _)
  obtain ⟨y, hy, hyk⟩ := hc.out (mem_image_of_mem f hx) (mem_image_of_mem f hx') ⟨h1.le, h2⟩
  exact hint y hy _ hyk

/-- If `β y` is not an integer for any `y ∈ (l, r)`, then `⌊β x⌋ = ⌊β x'⌋` for all
`x, x' ∈ (l, r)`. -/
@[zeta5irr "lem_ex_floor_const"]
theorem floor_mul_eq_floor_mul_of_mem_Ioo {β l r : ℝ} (hint : ∀ y ∈ Ioo l r, ∀ k : ℤ, β * y ≠ k)
    {x x' : ℝ} (hx : x ∈ Ioo l r) (hx' : x' ∈ Ioo l r) : ⌊β * x⌋ = ⌊β * x'⌋ :=
  floor_eq_floor_of_isPreconnected isPreconnected_Ioo
    (continuous_const.mul continuous_id).continuousOn hint hx hx'

end Zeta5Irr
