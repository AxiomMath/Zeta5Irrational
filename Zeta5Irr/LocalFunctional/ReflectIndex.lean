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
public import Mathlib.Order.Interval.Finset.Box
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
# The reflected index `d(r)`

For `r ∈ ℤ` put `d(r) = r` if `r ≥ 0` and `d(r) = -r - 1` if `r < 0`. This is a natural number
in either case, and it is the index of the harmonic sum `H_{d(r)}^{(5)}` that the functional `τ_X`
attaches to a simple pole at `r`. On the negative integers it is the reflection `r ↦ -1 - r`,
which exchanges the negative integers with the natural numbers.

## Main definitions

* `Zeta5Irr.reflectIndex`: the map `d : ℤ → ℕ`.

## Main results

* `Zeta5Irr.reflectIndex_of_nonneg`: `d(r) = r` for `r ≥ 0`.
* `Zeta5Irr.reflectIndex_of_neg`: `d(r) = -r - 1` for `r < 0`.

## Implementation notes

The codomain is `ℕ` rather than `ℤ`, since `d(r)` is used only as the index of the harmonic sum
`Zeta5Irr.harmonicFive`, which is indexed by `ℕ`. The definition is by the constructors of `ℤ`:
`Int.ofNat n ↦ n` and `Int.negSucc n ↦ n`, the latter because `Int.negSucc n = -n - 1`. The two
cases of the source are the lemmas `reflectIndex_of_nonneg` and `reflectIndex_of_neg`, stated
after the cast back to `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

/-- The reflected index `d(r)` of an integer `r`: `d(r) = r` if `r ≥ 0` and `d(r) = -r - 1` if
`r < 0`. -/
@[zeta5irr "def_dr"]
def reflectIndex : ℤ → ℕ
  | .ofNat n => n
  | .negSucc n => n

/-- `d(n) = n` for a natural number `n`. -/
@[simp]
theorem reflectIndex_natCast (n : ℕ) : reflectIndex n = n := rfl

/-- `d(-n - 1) = n` for a natural number `n`. -/
@[simp]
theorem reflectIndex_negSucc (n : ℕ) : reflectIndex (Int.negSucc n) = n := rfl

/-- `d(r) = r` for `r ≥ 0`. -/
@[zeta5irr "def_dr"]
theorem reflectIndex_of_nonneg {r : ℤ} (hr : 0 ≤ r) : (reflectIndex r : ℤ) = r := by
  lift r to ℕ using hr
  simp

/-- `d(r) = -r - 1` for `r < 0`. -/
@[zeta5irr "def_dr"]
theorem reflectIndex_of_neg {r : ℤ} (hr : r < 0) : (reflectIndex r : ℤ) = -r - 1 := by
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hr.le
  cases n with
  | zero => simp at hr
  | succ n =>
    rw [show -((n + 1 : ℕ) : ℤ) = Int.negSucc n from rfl, reflectIndex_negSucc, Int.negSucc_eq]
    ring

/-- `d(r) = r.toNat` for `r ≥ 0`. -/
theorem reflectIndex_eq_toNat {r : ℤ} (hr : 0 ≤ r) : reflectIndex r = r.toNat := by
  lift r to ℕ using hr
  simp

/-- `d(r) = (-r - 1).toNat` for `r < 0`. -/
theorem reflectIndex_eq_toNat_neg_sub_one {r : ℤ} (hr : r < 0) :
    reflectIndex r = (-r - 1).toNat := by
  have := reflectIndex_of_neg hr
  omega

end Zeta5Irr
