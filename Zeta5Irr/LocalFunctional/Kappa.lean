/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The weights `κ_d`

For `d ≥ 3` the weight is `κ_d = d (d - 1) (d - 2) B_{d-3} / 24`, and `κ_0 = κ_1 = κ_2 = 0`.
These are the values of the functional `τ(P) = L(P''') / 24` on the monomials `x^d`.

## Main definitions

* `Zeta5Irr.kappa`: the weight `κ_d ∈ ℚ`.

## Main results

* `Zeta5Irr.kappa_add_three`: `κ_{d+3} = (d + 3)(d + 2)(d + 1) B_d / 24`.
* `Zeta5Irr.kappa_of_three_le`: `κ_d = d (d - 1) (d - 2) B_{d-3} / 24` for `3 ≤ d`.
* `Zeta5Irr.kappa_of_lt_three`, `Zeta5Irr.kappa_zero`, `Zeta5Irr.kappa_one`,
  `Zeta5Irr.kappa_two`: `κ_0 = κ_1 = κ_2 = 0`.

## Implementation notes

* `B` is Mathlib's `bernoulli`, with the convention `B₁ = -1/2`.
* The factor `d (d - 1) (d - 2)` is written as the descending factorial `d.descFactorial 3`,
  which vanishes for `d < 3`; so a single formula covers both clauses of the definition.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

/-- The weight `κ_d = d (d - 1) (d - 2) B_{d-3} / 24`, which is `0` for `d < 3`. -/
@[zeta5irr "def_kappa"]
def kappa (d : ℕ) : ℚ :=
  d.descFactorial 3 * bernoulli (d - 3) / 24

/-- `κ_d = 0` for `d < 3`. -/
@[zeta5irr "def_kappa"]
theorem kappa_of_lt_three {d : ℕ} (hd : d < 3) : kappa d = 0 := by
  rw [kappa, Nat.descFactorial_eq_zero_iff_lt.2 hd]
  simp

/-- `κ_0 = 0`. -/
@[simp]
theorem kappa_zero : kappa 0 = 0 := kappa_of_lt_three (by norm_num)

/-- `κ_1 = 0`. -/
@[simp]
theorem kappa_one : kappa 1 = 0 := kappa_of_lt_three (by norm_num)

/-- `κ_2 = 0`. -/
@[simp]
theorem kappa_two : kappa 2 = 0 := kappa_of_lt_three (by norm_num)

/-- `κ_{d+3} = (d + 3)(d + 2)(d + 1) B_d / 24`. -/
theorem kappa_add_three (d : ℕ) :
    kappa (d + 3) = (d + 3) * (d + 2) * (d + 1) * bernoulli d / 24 := by
  have h : (d + 3).descFactorial 3 = (d + 3) * (d + 2) * (d + 1) := by
    simp [Nat.descFactorial]
    ring
  rw [kappa, h, Nat.add_sub_cancel]
  push_cast
  ring

/-- `κ_d = d (d - 1) (d - 2) B_{d-3} / 24` for `d ≥ 3`, with the subtractions in `ℚ`. -/
@[zeta5irr "def_kappa"]
theorem kappa_of_three_le {d : ℕ} (hd : 3 ≤ d) :
    kappa d = d * (d - 1) * (d - 2) * bernoulli (d - 3) / 24 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hd
  rw [kappa_add_three, Nat.add_sub_cancel]
  push_cast
  ring

end Zeta5Irr
