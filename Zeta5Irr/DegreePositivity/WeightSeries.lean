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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The series `∑ ℓ⁴ qˡ`

For a real `q` with `|q| < 1` this file evaluates the power series
`∑_{ℓ ≥ 1} ℓ⁴ qˡ = q (1 + 11 q + 11 q² + q³) / (1 - q)⁵`.
The coefficients `1, 11, 11, 1` are the Eulerian numbers of order `4`.

## Main results

* `Zeta5Irr.hasSum_natCast_pow_four_mul_pow`: the series has the stated sum.
* `Zeta5Irr.tsum_natCast_pow_four_mul_pow`: the value of the series.

## Implementation notes

* The source sums over `ℓ ≥ 1`; here the sum runs over all `ℓ : ℕ`, which is the same
  series since the `ℓ = 0` term `0⁴ q⁰` vanishes.
* The source assumes `0 < q < 1`; the identity holds under the weaker hypothesis `|q| < 1`.
* The proof specialises the general formula `∑ n^k rⁿ = ∑_{j ≤ k} S(k, j) j! rʲ / (1 - r)^{j+1}`,
  with `S(k, j)` the Stirling numbers of the second kind, to `k = 4`, where
  `(S(4, j))_{j ≤ 4} = (0, 1, 7, 6, 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `|q| < 1`, `∑ ℓ⁴ qˡ = q (1 + 11 q + 11 q² + q³) / (1 - q)⁵`, as a `HasSum`. -/
theorem hasSum_natCast_pow_four_mul_pow {q : ℝ} (hq : |q| < 1) :
    HasSum (fun ℓ : ℕ => (ℓ : ℝ) ^ 4 * q ^ ℓ)
      (q * (1 + 11 * q + 11 * q ^ 2 + q ^ 3) / (1 - q) ^ 5) := by
  convert hasSum_pow_mul_geometric_of_norm_lt_one 4 (by rwa [Real.norm_eq_abs]) using 1
  have h1q : 1 - q ≠ 0 := by linarith [le_abs_self q]
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Nat.stirlingSecond, CharP.cast_eq_zero, Nat.factorial, Nat.cast_one, mul_one, pow_zero,
    zero_add, pow_one, zero_div, mul_zero, add_zero, Nat.succ_eq_add_one, one_mul, Nat.reduceMul,
    Nat.cast_ofNat]
  field_simp
  ring

/-- For `|q| < 1`, `∑_{ℓ ≥ 1} ℓ⁴ qˡ = q (1 + 11 q + 11 q² + q³) / (1 - q)⁵`
(the `ℓ = 0` term vanishes). -/
@[zeta5irr "lem_w_series"]
theorem tsum_natCast_pow_four_mul_pow {q : ℝ} (hq : |q| < 1) :
    ∑' ℓ : ℕ, (ℓ : ℝ) ^ 4 * q ^ ℓ = q * (1 + 11 * q + 11 * q ^ 2 + q ^ 3) / (1 - q) ^ 5 :=
  (hasSum_natCast_pow_four_mul_pow hq).tsum_eq

end Zeta5Irr
