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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The logarithmic enclosure polynomial `Λ_m`

For `m : ℕ` the polynomial
`Λ_m(z) = 2 ∑_{k=0}^{m-1} z^{2k+1} / (2k+1)`
is the `m`-th partial sum of the odd power series of `log ((1 + z) / (1 - z))`. On `0 ≤ z < 1`
it is a lower bound for that logarithm, with error at most `2 z^{2m+1} / (1 - z²)`; these give
rational enclosures of logarithms.

## Main definitions

* `Zeta5Irr.logApprox`: the polynomial `Λ_m(z)`.

## Main results

* `Zeta5Irr.logApprox_zero`, `Zeta5Irr.logApprox_succ`: the recursion in `m`.
* `Zeta5Irr.ratCast_logApprox`: `Λ_m` commutes with the cast from `ℚ`.
* `Zeta5Irr.logApprox_nonneg`: `0 ≤ Λ_m(z)` for `0 ≤ z`.
* `Zeta5Irr.logApprox_le_log`: `Λ_m(z) ≤ log ((1 + z) / (1 - z))` for `0 ≤ z < 1`.
* `Zeta5Irr.abs_log_sub_logApprox_le`: the error bound `2 |z|^{2m+1} / (1 - z²)` for `|z| < 1`.

## Implementation notes

* The source states the definition for `0 ≤ z < 1` and `m ≥ 1`. Being a polynomial, `Λ_m` is
  defined here for every `z` in any division ring and every `m : ℕ`, with `Λ_0 = 0`; the
  hypotheses appear only in the lemmas that need them. Over `ℚ` it is computable.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.4: elementary enclosures.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

variable {K : Type*}

/-- The logarithmic enclosure polynomial `Λ_m(z) = 2 ∑_{k<m} z^{2k+1} / (2k+1)`, the `m`-th
partial sum of the power series of `log ((1 + z) / (1 - z))`. -/
@[zeta5irr "def_enc_log"]
def logApprox [DivisionRing K] (m : ℕ) (z : K) : K :=
  2 * ∑ k ∈ range m, z ^ (2 * k + 1) / (2 * k + 1)

section DivisionRing

variable [DivisionRing K]

/-- `Λ_0 = 0`. -/
@[simp]
theorem logApprox_zero (z : K) : logApprox 0 z = 0 := by
  simp [logApprox]

/-- The recursion `Λ_{m+1}(z) = Λ_m(z) + 2 z^{2m+1} / (2m+1)`. -/
theorem logApprox_succ (m : ℕ) (z : K) :
    logApprox (m + 1) z = logApprox m z + 2 * (z ^ (2 * m + 1) / (2 * m + 1)) := by
  simp [logApprox, sum_range_succ, mul_add]

/-- `Λ_m(0) = 0`. -/
@[simp]
theorem logApprox_at_zero (m : ℕ) : logApprox m (0 : K) = 0 := by
  simp [logApprox]

end DivisionRing

/-- `Λ_m` commutes with the cast from `ℚ` into a field of characteristic zero. -/
@[simp, norm_cast]
theorem ratCast_logApprox [Field K] [CharZero K] (m : ℕ) (z : ℚ) :
    ((logApprox m z : ℚ) : K) = logApprox m (z : K) := by
  simp [logApprox]

/-- `Λ_m(z)` is nonnegative for `z ≥ 0`. -/
theorem logApprox_nonneg [Field K] [LinearOrder K] [IsStrictOrderedRing K] {z : K} (hz : 0 ≤ z)
    (m : ℕ) : 0 ≤ logApprox m z := by
  unfold logApprox
  positivity

/-- For `0 ≤ z < 1`, `Λ_m(z) ≤ log ((1 + z) / (1 - z))`. -/
theorem logApprox_le_log {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) (m : ℕ) :
    logApprox m z ≤ Real.log ((1 + z) / (1 - z)) := by
  have := Real.sum_range_le_log_div h₀ h₁ m
  unfold logApprox
  linarith

/-- For `|z| < 1`, `|log ((1 + z) / (1 - z)) - Λ_m(z)| ≤ 2 |z|^{2m+1} / (1 - z²)`. -/
theorem abs_log_sub_logApprox_le {z : ℝ} (h : |z| < 1) (m : ℕ) :
    |Real.log ((1 + z) / (1 - z)) - logApprox m z| ≤ 2 * (|z| ^ (2 * m + 1) / (1 - z ^ 2)) := by
  have := Real.sum_range_sub_log_div_le h m
  have e : Real.log ((1 + z) / (1 - z)) - logApprox m z =
      2 * (1 / 2 * Real.log ((1 + z) / (1 - z)) -
        ∑ i ∈ range m, z ^ (2 * i + 1) / (2 * i + 1)) := by
    unfold logApprox; ring
  rw [e, abs_mul, abs_two]
  linarith

end Zeta5Irr
