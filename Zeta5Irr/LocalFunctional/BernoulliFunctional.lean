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
# The Bernoulli functional

The Bernoulli functional `L : ℚ[X] → ℚ` is the `ℚ`-linear map sending the monomial `X ^ k` to
the Bernoulli number `B_k`, with the convention `B_1 = -1/2`. It is the "umbral" evaluation that
replaces each power `x ^ k` by `B_k`, so `L (∑ aₖ X ^ k) = ∑ aₖ B_k`.

## Main definitions

* `Zeta5Irr.bernoulliFunctional`: the `ℚ`-linear map `L : ℚ[X] →ₗ[ℚ] ℚ` with `L (X ^ k) = B_k`.

## Main results

* `Zeta5Irr.bernoulliFunctional_X_pow`: `L (X ^ k) = bernoulli k`.
* `Zeta5Irr.bernoulliFunctional_apply`: `L p = ∑ₖ (coeff p k) * B_k`.

## Implementation notes

The Bernoulli numbers are Mathlib's `bernoulli`, which follows the convention `B_1 = -1/2`
(see `bernoulli_one`), as opposed to `bernoulli'`, which has `B_1 = 1/2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C monomial lsum_apply monomial_one_right_eq_X_pow C_mul_X_pow_eq_monomial)

/-- The Bernoulli functional `L : ℚ[X] →ₗ[ℚ] ℚ`, the `ℚ`-linear map with `L (X ^ k) = B_k`
for every `k`, where `B_k = bernoulli k` (so `B_1 = -1/2`). -/
@[zeta5irr "def_L"]
noncomputable def bernoulliFunctional : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun k => bernoulli k • LinearMap.id

/-- `L` replaces each coefficient `aₖ` of `X ^ k` by `aₖ * B_k` and sums: `L p = ∑ₖ aₖ B_k`. -/
theorem bernoulliFunctional_apply (p : ℚ[X]) :
    bernoulliFunctional p = p.sum fun k a => a * bernoulli k := by
  simp only [bernoulliFunctional, lsum_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, mul_comm]

/-- `L (a X ^ k) = a B_k`, stated for `monomial k a`. -/
@[simp]
theorem bernoulliFunctional_monomial (k : ℕ) (a : ℚ) :
    bernoulliFunctional (monomial k a) = a * bernoulli k := by
  simp [bernoulliFunctional_apply]

/-- The characterising property of the Bernoulli functional: `L (X ^ k) = B_k`. -/
@[zeta5irr "def_L", simp]
theorem bernoulliFunctional_X_pow (k : ℕ) : bernoulliFunctional (X ^ k) = bernoulli k := by
  simp [← monomial_one_right_eq_X_pow]

/-- `L (C a * X ^ k) = a B_k`. -/
@[simp]
theorem bernoulliFunctional_C_mul_X_pow (a : ℚ) (k : ℕ) :
    bernoulliFunctional (C a * X ^ k) = a * bernoulli k := by
  simp [C_mul_X_pow_eq_monomial]

/-- On constants `L` is the identity, since `B_0 = 1`. -/
@[simp]
theorem bernoulliFunctional_C (a : ℚ) : bernoulliFunctional (C a) = a := by
  simpa using bernoulliFunctional_C_mul_X_pow a 0

/-- `L 1 = B_0 = 1`. -/
@[simp]
theorem bernoulliFunctional_one : bernoulliFunctional 1 = 1 := by
  simpa using bernoulliFunctional_X_pow 0

/-- `L X = B_1 = -1/2`. -/
@[simp]
theorem bernoulliFunctional_X : bernoulliFunctional X = -1 / 2 := by
  simpa using bernoulliFunctional_X_pow 1

/-- A linear functional on `ℚ[X]` agreeing with `L` on every monomial `X ^ k` is `L`. -/
theorem eq_bernoulliFunctional_of_X_pow {f : ℚ[X] →ₗ[ℚ] ℚ}
    (hf : ∀ k : ℕ, f (X ^ k) = bernoulli k) : f = bernoulliFunctional := by
  ext k
  simpa [monomial_one_right_eq_X_pow] using hf k

end Zeta5Irr
