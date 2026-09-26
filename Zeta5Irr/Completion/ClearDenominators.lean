/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.DenomsClearable
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
public import Mathlib.Topology.Sheaves.Init

/-!
# Clearing the denominator of a polynomial value at a rational point

Let `P ∈ ℤ[X]` have degree at most `d`, let `a ∈ ℤ` and let `b` be a nonzero integer. Writing
`P = ∑_{k ≤ d} c_k X^k`, we have `b^d P(a/b) = ∑_{k ≤ d} c_k a^k b^{d-k}`, which is an integer.

## Main results

* `Zeta5Irr.exists_int_eq_pow_mul_eval_div`: `b ^ d * P(a / b)` is an integer.

## Implementation notes

The source states the result for `b > 0` and values in `ℚ`. We assume only `b ≠ 0`, and evaluate
in an arbitrary field `K` of characteristic zero (so that `b` stays nonzero in `K`); `K = ℚ`
recovers the source's statement and `K = ℝ` the form used when the polynomial is evaluated
at a real point. The proof is `denomsClearable_of_natDegree_le` from Mathlib.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10 (completion of the irrationality proof).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- If `P ∈ ℤ[X]` has degree at most `d`, `a ∈ ℤ` and `b ∈ ℤ` is nonzero, then `b ^ d * P(a / b)`
is an integer, the value being taken in any field of characteristic zero. -/
@[zeta5irr "lem_final_clear"]
theorem exists_int_eq_pow_mul_eval_div {K : Type*} [Field K] [CharZero K] {d : ℕ} {P : ℤ[X]}
    (hP : P.natDegree ≤ d) (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    ∃ z : ℤ, (b : K) ^ d * (P.map (Int.castRingHom K)).eval ((a : K) / b) = z := by
  have hb' : (b : K)⁻¹ * Int.castRingHom K b = 1 := inv_mul_cancel₀ (by exact_mod_cast hb)
  obtain ⟨D, bi, hbi, hD⟩ := denomsClearable_of_natDegree_le d a hb' P hP
  obtain rfl : bi = (b : K)⁻¹ := eq_inv_of_mul_eq_one_left hbi
  exact ⟨D, by simpa [div_eq_mul_inv] using hD.symm⟩

end Zeta5Irr
