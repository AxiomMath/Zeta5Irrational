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
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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
# Primes `p` with `p ≤ 5K < p²` have `⌊log_p (5K)⌋ = 1`

If `b > 1` and `b ≤ x < b²`, then `1 ≤ log_b x < 2`, so `⌊log_b x⌋ = 1`. Applied to a prime `p`
and `x = 5K`, this says that the primes in the range `√(5K) < p ≤ 5K` contribute exactly the
first power of `p` to the normalizing factor.

## Main results

* `Zeta5Irr.floor_logb_eq_one`: if `1 < b` and `b ≤ x < b ^ 2`, then `⌊logb b x⌋ = 1`.
* `Zeta5Irr.floor_logb_five_mul_eq_one`: if `p` is prime and `p ≤ 5K < p ^ 2`, then
  `⌊logb p (5K)⌋ = 1`.

## Implementation notes

* The source assumes `K ≥ 1`; the argument does not use it, so the hypothesis is dropped.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8: the growth of the normalizing factor.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- If `1 < b` and `b ≤ x < b ^ 2`, then `⌊log_b x⌋ = 1`. -/
theorem floor_logb_eq_one {b x : ℝ} (hb : 1 < b) (hbx : b ≤ x) (hxb : x < b ^ 2) :
    ⌊logb b x⌋ = 1 := by
  have hx : 0 < x := (zero_lt_one.trans hb).trans_le hbx
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_logb_iff_rpow_le hb hx, rpow_one]
    exact hbx
  · rw [logb_lt_iff_lt_rpow hb hx]
    norm_num
    exact hxb

/-- Let `p` be a prime with `p ^ 2 > 5K` and `p ≤ 5K`. Then `⌊log_p (5K)⌋ = 1`. -/
@[zeta5irr "lem_norm_logp_one"]
theorem floor_logb_five_mul_eq_one {K : ℝ} {p : ℕ} (hp : p.Prime) (hpK : 5 * K < (p : ℝ) ^ 2)
    (hKp : (p : ℝ) ≤ 5 * K) : ⌊logb p (5 * K)⌋ = 1 :=
  floor_logb_eq_one (by exact_mod_cast hp.one_lt) hKp hpK

end Zeta5Irr
