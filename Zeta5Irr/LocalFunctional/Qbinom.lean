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
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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
# The binomial polynomial `(x choose k)`

For `k ≥ 0` the binomial polynomial is
`(x choose k) = (1 / k!) ∏_{i=0}^{k-1} (x - i) ∈ ℚ[x]`, so that `(x choose 0) = 1`.
It is the falling factorial `x (x - 1) ⋯ (x - k + 1)` divided by `k!`.

## Main definitions

* `Zeta5Irr.qbinom`: the binomial polynomial `(x choose k) ∈ ℚ[x]`.

## Main results

* `Zeta5Irr.qbinom_zero`: `(x choose 0) = 1`.
* `Zeta5Irr.factorial_smul_qbinom`: `k! • (x choose k)` is the falling factorial.
* `Zeta5Irr.eval_qbinom`: the product formula for the value at `x`.
* `Zeta5Irr.eval_qbinom_eq_choose`: the value at `x ∈ ℚ` is `Ring.choose x k`.
* `Zeta5Irr.eval_intCast_qbinom`: the value at an integer is the integer `Ring.choose n k`.
* `Zeta5Irr.eval_natCast_qbinom`: the value at a natural number `n` is `n.choose k`.
* `Zeta5Irr.natDegree_qbinom`, `Zeta5Irr.leadingCoeff_qbinom`: degree `k`, leading
  coefficient `1 / k!`.

## Implementation notes

* The polynomial is built from Mathlib's falling factorial `descPochhammer ℚ k`, whose value
  at `x` is `∏_{i < k} (x - i)`. Mathlib's `Ring.choose` is the scalar function in a binomial
  ring; here a genuine polynomial is needed, and `Zeta5Irr.eval_qbinom_eq_choose` connects the
  two.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6: small primes.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Nat

/-- The binomial polynomial `(x choose k) = (1 / k!) ∏_{i=0}^{k-1} (x - i) ∈ ℚ[x]`. -/
@[zeta5irr "def_qbinom"]
noncomputable def qbinom (k : ℕ) : ℚ[X] := (k ! : ℚ)⁻¹ • descPochhammer ℚ k

/-- `(x choose 0) = 1`. -/
@[simp]
theorem qbinom_zero : qbinom 0 = 1 := by
  simp [qbinom]

/-- `k! • (x choose k)` is the falling factorial `x (x - 1) ⋯ (x - k + 1)`. -/
theorem factorial_smul_qbinom (k : ℕ) : (k ! : ℚ) • qbinom k = descPochhammer ℚ k := by
  rw [qbinom, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- The value of `(x choose k)` at `x` is `(1 / k!) ∏_{i=0}^{k-1} (x - i)`. -/
theorem eval_qbinom (k : ℕ) (x : ℚ) :
    (qbinom k).eval x = (k ! : ℚ)⁻¹ * ∏ i ∈ Finset.range k, (x - i) := by
  rw [qbinom, eval_smul, smul_eq_mul, descPochhammer_eval_eq_prod_range]

/-- The value of `(x choose k)` at `x ∈ ℚ` is the generalized binomial coefficient
`Ring.choose x k`. -/
theorem eval_qbinom_eq_choose (k : ℕ) (x : ℚ) : (qbinom k).eval x = Ring.choose x k := by
  rw [Ring.choose_eq_smul, qbinom, eval_smul, ← aeval_eq_smeval, aeval_def, ← eval_map,
    descPochhammer_map]

/-- The value of `(x choose k)` at an integer `n` is the integer `Ring.choose n k`. -/
@[zeta5irr "lem_small_choose_int"]
theorem eval_intCast_qbinom (k : ℕ) (n : ℤ) :
    (qbinom k).eval (n : ℚ) = (Ring.choose n k : ℤ) := by
  rw [eval_qbinom_eq_choose, ← eq_intCast (Int.castRingHom ℚ) n, ← Ring.map_choose, eq_intCast]

/-- The value of `(x choose k)` at a natural number `n` is `n.choose k`. -/
theorem eval_natCast_qbinom (k n : ℕ) : (qbinom k).eval (n : ℚ) = n.choose k := by
  rw [qbinom, eval_smul, smul_eq_mul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `(x choose k)` has degree `k`. -/
@[simp]
theorem natDegree_qbinom (k : ℕ) : (qbinom k).natDegree = k := by
  rw [qbinom, natDegree_smul _ (by positivity), descPochhammer_natDegree]

/-- The leading coefficient of `(x choose k)` is `1 / k!`. -/
@[simp]
theorem leadingCoeff_qbinom (k : ℕ) : (qbinom k).leadingCoeff = (k ! : ℚ)⁻¹ := by
  rw [qbinom, leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero (by positivity)),
    (monic_descPochhammer ℚ k).leadingCoeff, smul_eq_mul, mul_one]

end Zeta5Irr
