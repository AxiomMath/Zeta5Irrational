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
# The derivative numerators

The derivatives of `f(y) = 1 / (e^{2πy} - 1)` are, after the substitution `q = e^{-2πy}`,
of the form `(-2π)^k q Φ_k(q) / (1 - q)^{k+1}` for integer polynomials `Φ_k`. Writing
`G_k(q) = q Φ_k(q) / (1 - q)^{k+1}`, the relation `q G_k' = G_{k+1}` forces
`Φ_0 = 1` and the recurrence
`Φ_{k+1}(q) = (q Φ_k(q))' (1 - q) + (k + 1) q Φ_k(q)`,
whose first five members are
`Φ_0 = 1`, `Φ_1 = 1`, `Φ_2 = 1 + q`, `Φ_3 = 1 + 4q + q²`, `Φ_4 = 1 + 11q + 11q² + q³`.
These are the Eulerian polynomials.

## Main definitions

* `Zeta5Irr.derivNumerator`: the polynomials `Φ_k ∈ ℤ[q]`.

## Main results

* `Zeta5Irr.derivNumerator_succ`, `Zeta5Irr.derivNumerator_succ'`: the recurrence, in the
  quotient-rule form and in the expanded form
  `Φ_{k+1} = (1 + k q) Φ_k + q (1 - q) Φ_k'`.
* `Zeta5Irr.derivNumerator_zero`, …, `Zeta5Irr.derivNumerator_four`: the five explicit
  members `Φ_0, …, Φ_4`, with their evaluations `Zeta5Irr.aeval_derivNumerator_zero`, ….
* `Zeta5Irr.aeval_derivNumerator_pos`, `Zeta5Irr.aeval_derivNumerator_le`: for `k ≤ 4` and
  `0 ≤ q ≤ 1` one has `0 < Φ_k(q) ≤ 24`.

## Implementation notes

The source defines `Φ` as the list of its five members `Φ_0, …, Φ_4`. We define instead the
whole sequence `ℕ → ℤ[X]` by the recurrence satisfied by these members, and recover the five
listed polynomials as the lemmas `derivNumerator_zero`, …, `derivNumerator_four`. On
`0 ≤ k ≤ 4` this is exactly the source's family; the recurrence is then a definitional
unfolding, which is what the inductive proof of the derivative formula consumes, and that
proof goes through for every `k` rather than only `k ≤ 4`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The derivative numerators `Φ_k ∈ ℤ[q]`: `Φ_0 = 1` and
`Φ_{k+1}(q) = (q Φ_k(q))' (1 - q) + (k + 1) q Φ_k(q)`. The first five are
`1, 1, 1 + q, 1 + 4q + q², 1 + 11q + 11q² + q³` (the Eulerian polynomials). -/
@[zeta5irr "def_wA"]
noncomputable def derivNumerator : ℕ → ℤ[X]
  | 0 => 1
  | k + 1 => derivative (X * derivNumerator k) * (1 - X) +
      ((k + 1 : ℕ) : ℤ[X]) * X * derivNumerator k

/-- The zeroth derivative numerator: `Φ_0 = 1`. -/
@[simp]
theorem derivNumerator_zero : derivNumerator 0 = 1 := rfl

/-- The recurrence for `Φ` in the quotient-rule form
`Φ_{k+1} = (q Φ_k)' (1 - q) + (k + 1) q Φ_k`. -/
theorem derivNumerator_succ (k : ℕ) :
    derivNumerator (k + 1) = derivative (X * derivNumerator k) * (1 - X) +
      ((k + 1 : ℕ) : ℤ[X]) * X * derivNumerator k := rfl

/-- The recurrence for `Φ` in expanded form `Φ_{k+1} = (1 + k q) Φ_k + q (1 - q) Φ_k'`. -/
theorem derivNumerator_succ' (k : ℕ) :
    derivNumerator (k + 1) = (1 + (k : ℤ[X]) * X) * derivNumerator k +
      X * (1 - X) * derivative (derivNumerator k) := by
  rw [derivNumerator_succ, derivative_mul, derivative_X]
  push_cast
  ring

/-- The first derivative numerator: `Φ_1 = 1`. -/
@[simp]
theorem derivNumerator_one : derivNumerator 1 = 1 := by
  simp [derivNumerator_succ']

/-- The second derivative numerator: `Φ_2 = 1 + q`. -/
@[simp]
theorem derivNumerator_two : derivNumerator 2 = 1 + X := by
  rw [derivNumerator_succ', derivNumerator_one]
  simp

/-- The third derivative numerator: `Φ_3 = 1 + 4q + q²`. -/
@[simp]
theorem derivNumerator_three : derivNumerator 3 = 1 + 4 * X + X ^ 2 := by
  rw [derivNumerator_succ', derivNumerator_two]
  simp
  ring

/-- The fourth derivative numerator: `Φ_4 = 1 + 11q + 11q² + q³`. -/
@[simp]
theorem derivNumerator_four : derivNumerator 4 = 1 + 11 * X + 11 * X ^ 2 + X ^ 3 := by
  rw [derivNumerator_succ', derivNumerator_three]
  simp
  ring

section aeval

variable {R : Type*} [CommRing R] (q : R)

/-- Evaluation of `Φ_0` at `q`: `Φ_0(q) = 1`. -/
theorem aeval_derivNumerator_zero : aeval q (derivNumerator 0) = 1 := by simp

/-- Evaluation of `Φ_1` at `q`: `Φ_1(q) = 1`. -/
theorem aeval_derivNumerator_one : aeval q (derivNumerator 1) = 1 := by simp

/-- Evaluation of `Φ_2` at `q`: `Φ_2(q) = 1 + q`. -/
theorem aeval_derivNumerator_two : aeval q (derivNumerator 2) = 1 + q := by simp

/-- Evaluation of `Φ_3` at `q`: `Φ_3(q) = 1 + 4q + q²`. -/
theorem aeval_derivNumerator_three : aeval q (derivNumerator 3) = 1 + 4 * q + q ^ 2 := by
  simp [map_ofNat]

/-- Evaluation of `Φ_4` at `q`: `Φ_4(q) = 1 + 11q + 11q² + q³`. -/
theorem aeval_derivNumerator_four :
    aeval q (derivNumerator 4) = 1 + 11 * q + 11 * q ^ 2 + q ^ 3 := by
  simp [map_ofNat]

end aeval

section bounds

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {q : R}

/-- For `k ≤ 4` and `q ≥ 0`, `Φ_k(q) > 0`. -/
theorem aeval_derivNumerator_pos {k : ℕ} (hk : k ≤ 4) (hq : 0 ≤ q) :
    0 < aeval q (derivNumerator k) := by
  interval_cases k <;>
    simp only [aeval_derivNumerator_zero, aeval_derivNumerator_one, aeval_derivNumerator_two,
      aeval_derivNumerator_three, aeval_derivNumerator_four] <;> positivity

/-- For `k ≤ 4` and `0 ≤ q ≤ 1`, `Φ_k(q) ≤ 24`. -/
theorem aeval_derivNumerator_le {k : ℕ} (hk : k ≤ 4) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    aeval q (derivNumerator k) ≤ 24 := by
  have h2 : q ^ 2 ≤ 1 := pow_le_one₀ hq₀ hq₁
  have h3 : q ^ 3 ≤ 1 := pow_le_one₀ hq₀ hq₁
  interval_cases k <;>
    simp only [aeval_derivNumerator_zero, aeval_derivNumerator_one, aeval_derivNumerator_two,
      aeval_derivNumerator_three, aeval_derivNumerator_four] <;> linarith

end bounds

end Zeta5Irr
