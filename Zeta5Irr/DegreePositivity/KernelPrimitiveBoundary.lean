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
# The primitive vanishes to order five at the origin

For `b > 0` the function `y ↦ y ^ 5 / (y ^ 2 + b ^ 2)` vanishes to order five at `y = 0`:
for every `0 ≤ m ≤ 4`, the quotient `y ^ (m - 5) (d/dy)^m (y ^ 5 / (y ^ 2 + b ^ 2))` is
bounded on `(0, 1]`.

This is an instance of a general fact: if `h` is smooth and `m ≤ n`, then
`y ^ (m - n) (d/dy)^m (y ^ n h(y))` is bounded on `(0, 1]`. By the Leibniz rule the
`m`-th derivative of `y ^ n h(y)` is
`∑_{i ≤ m} (m choose i) n! / (n - i)! y ^ (n - i) h^{(m - i)}(y)`, and multiplying by
`y ^ (m - n)` gives `∑_{i ≤ m} (m choose i) n! / (n - i)! y ^ (m - i) h^{(m - i)}(y)`, a
continuous function on the compact interval `[0, 1]`.

## Main results

* `Zeta5Irr.exists_bound_zpow_mul_iteratedDeriv_pow_mul`: for smooth `h` and `m ≤ n`,
  `y ^ (m - n) (d/dy)^m (y ^ n h(y))` is bounded on `(0, 1]`.
* `Zeta5Irr.exists_bound_zpow_mul_iteratedDeriv_kernelPrimitive`: the case
  `h(y) = (y ^ 2 + b ^ 2)⁻¹`, `n = 5`, `m ≤ 4`.

## Implementation notes

The source assumes `b > 0`; only `b ≠ 0` is used, since it makes `y ^ 2 + b ^ 2` nonzero
on all of `ℝ`, and the main result is stated under that hypothesis. The power `y ^ (m - 5)`
is the integer power `y ^ ((m : ℤ) - 5)`, and boundedness on `(0, 1]` is stated as the
existence of a constant `C` with `|…| ≤ C` for all `y ∈ Set.Ioc 0 1`. The general lemma
allows any `m ≤ n`, which is what the Leibniz argument uses; the source's range `m ≤ 4`
for `n = 5` is a special case.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Set

namespace Zeta5Irr

/-- If `h` is smooth and `m ≤ n`, then `y ^ (m - n) (d/dy)^m (y ^ n h(y))` is bounded on
`(0, 1]`: the function `y ^ n h(y)` vanishes to order `n` at the origin. -/
theorem exists_bound_zpow_mul_iteratedDeriv_pow_mul {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h)
    {n m : ℕ} (hm : m ≤ n) :
    ∃ C, ∀ y ∈ Ioc (0 : ℝ) 1,
      |y ^ ((m : ℤ) - n) * iteratedDeriv m (fun y => y ^ n * h y) y| ≤ C := by
  set g : ℝ → ℝ := fun y => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * (n.descFactorial i : ℝ) * (y ^ (m - i) * iteratedDeriv (m - i) h y)
  have hgc : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact continuous_const.mul ((continuous_pow _).mul
      (hh.continuous_iteratedDeriv _ (by exact_mod_cast le_top)))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨C, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := hy.1.ne'
  convert hC y (Ioc_subset_Icc_self hy) using 1
  rw [Real.norm_eq_abs]
  congr 1
  have hmul : (fun y : ℝ => y ^ n * h y) = (fun y : ℝ => y ^ n) * h := rfl
  have hpow : ContDiff ℝ ⊤ fun y : ℝ => y ^ n := contDiff_id.pow n
  rw [hmul, iteratedDeriv_mul (hpow.of_le le_top).contDiffAt (hh.of_le le_top).contDiffAt,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedDeriv_pow]
  have : y ^ ((m : ℤ) - n) * y ^ (n - i) = y ^ (m - i) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hy0]
    congr 1
    push_cast [him, him.trans hm]
    ring
  rw [← this]
  ring

/-- **The primitive vanishes to order five at the origin.** For `b ≠ 0` and `m ≤ 4`, the
function `y ↦ y ^ (m - 5) (d/dy)^m (y ^ 5 / (y ^ 2 + b ^ 2))` is bounded on `(0, 1]`. -/
@[zeta5irr "lem_w_ker_bdry"]
theorem exists_bound_zpow_mul_iteratedDeriv_kernelPrimitive {b : ℝ} (hb : b ≠ 0) {m : ℕ}
    (hm : m ≤ 4) :
    ∃ C, ∀ y ∈ Ioc (0 : ℝ) 1,
      |y ^ ((m : ℤ) - 5) * iteratedDeriv m (fun y : ℝ => y ^ 5 / (y ^ 2 + b ^ 2)) y| ≤ C := by
  have hh : ContDiff ℝ ⊤ fun y : ℝ => (y ^ 2 + b ^ 2)⁻¹ :=
    ((contDiff_id.pow 2).add contDiff_const).inv fun y => by positivity
  simpa [div_eq_mul_inv] using
    exists_bound_zpow_mul_iteratedDeriv_pow_mul hh (n := 5) (m := m) (by omega)

end Zeta5Irr
