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
public import Mathlib.NumberTheory.Padics.LocalField
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
# Integer-valued polynomials map `ℤ_p` into `ℤ_p`

Let `p` be a prime and let `A ∈ ℚ[x]` take integer values at every integer. Then `A(ℤ_p) ⊆ ℤ_p`.
Indeed `x ↦ ‖A(x)‖_p` is continuous on `ℤ_p`, so `{x ∈ ℤ_p | ‖A(x)‖_p ≤ 1}` is closed; it
contains the integers, which are dense in `ℤ_p`, hence it is all of `ℤ_p`.

## Main results

* `Zeta5Irr.norm_aeval_padicInt_le_one`: `‖A(x)‖_p ≤ 1` for every `x ∈ ℤ_p`.
* `Zeta5Irr.exists_padicInt_eq_aeval`: `A(x)` is the image of a `p`-adic integer.

## Implementation notes

The value `A(x)` for `x ∈ ℤ_p` is `Polynomial.aeval (x : ℚ_[p]) A`, the evaluation of `A` in the
`ℚ`-algebra `ℚ_p`. Membership in `ℤ_p` is stated as `‖A(x)‖ ≤ 1`, which is how `ℤ_[p]` is defined
as a subtype of `ℚ_[p]`; the literal form follows at once.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- A rational polynomial taking integer values at the integers maps `ℤ_p` into `ℤ_p`:
`‖A(x)‖_p ≤ 1` for every `p`-adic integer `x`. -/
@[zeta5irr "lem_small_intval"]
theorem norm_aeval_padicInt_le_one {p : ℕ} [Fact p.Prime] {A : ℚ[X]}
    (hA : ∀ m : ℤ, ∃ n : ℤ, A.eval (m : ℚ) = n) (x : ℤ_[p]) :
    ‖aeval (x : ℚ_[p]) A‖ ≤ 1 := by
  refine PadicInt.denseRange_intCast.induction_on x
    (isClosed_le (by fun_prop) continuous_const) fun m => ?_
  obtain ⟨n, hn⟩ := hA m
  have h : aeval ((m : ℤ_[p]) : ℚ_[p]) A = ((n : ℚ) : ℚ_[p]) := by
    rw [PadicInt.coe_intCast, ← Rat.cast_intCast, ← eq_ratCast (algebraMap ℚ ℚ_[p]),
      aeval_algebraMap_apply, coe_aeval_eq_eval, hn, eq_ratCast]
  simp only [h, Rat.cast_intCast]
  exact Padic.norm_int_le_one n

/-- A rational polynomial taking integer values at the integers maps `ℤ_p` into `ℤ_p`:
`A(x)` is the image of a `p`-adic integer for every `p`-adic integer `x`. -/
theorem exists_padicInt_eq_aeval {p : ℕ} [Fact p.Prime] {A : ℚ[X]}
    (hA : ∀ m : ℤ, ∃ n : ℤ, A.eval (m : ℚ) = n) (x : ℤ_[p]) :
    ∃ y : ℤ_[p], (y : ℚ_[p]) = aeval (x : ℚ_[p]) A :=
  ⟨⟨_, norm_aeval_padicInt_le_one hA x⟩, rfl⟩

end Zeta5Irr
