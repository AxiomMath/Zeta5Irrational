/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.NumberTheory.Padics.PadicNumbers
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The negative power sum `∑_{a=1}^{p-1} a⁻⁴` is divisible by `p`

Let `p` be a prime. For `1 ≤ k < p - 1` the power sum `∑_{a=1}^{p-1} a^{-k}` lies in `p ℤ_p`.
Indeed each `a` with `1 ≤ a ≤ p - 1` is a `p`-adic unit, and Fermat's little theorem gives
`a^{-k} ≡ a^{p-1-k} (mod p)`. The integer `∑_{a=1}^{p-1} a^{p-1-k}` reduces modulo `p` to
`∑_{x ∈ 𝔽_p} x^{p-1-k}` (the term `x = 0` vanishes as `p - 1 - k ≥ 1`), which is zero because
`p - 1 - k < p - 1`. The case `k = 4`, which needs `p ≥ 7`, is the statement used in the
distribution property of the local functional.

## Main results

* `Zeta5Irr.norm_sum_inv_pow_le`: `‖∑_{a=1}^{p-1} a^{-k}‖_p ≤ p⁻¹` for `1 ≤ k < p - 1`.
* `Zeta5Irr.norm_sum_inv_pow_four_le`: `‖∑_{a=1}^{p-1} a^{-4}‖_p ≤ p⁻¹` for `p ≥ 7`.

## Implementation notes

The sum is formed in `ℚ_[p]`, and membership in `p ℤ_p` is expressed as `‖x‖ ≤ p⁻¹`, which for
`x ∈ ℚ_[p]` is equivalent to `x ∈ p ℤ_p` and has no exceptional case at `x = 0`. The source's
statement is the case `k = 4`; the general exponent costs nothing in the proof.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`, distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For a prime `p` and `1 ≤ m < p - 1`, the prime `p` divides `∑_{a=1}^{p-1} a^m`. -/
theorem prime_dvd_sum_Icc_pow (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) (hm' : m < p - 1) :
    (p : ℤ) ∣ ∑ a ∈ Icc 1 (p - 1), (a : ℤ) ^ m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hp := (Fact.out : p.Prime).pos
  have h1 : ∑ a ∈ Icc 1 (p - 1), (a : ZMod p) ^ m = ∑ a ∈ range p, (a : ZMod p) ^ m := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hp]
    simp [zero_pow (by omega : m ≠ 0)]
    rfl
  rw [h1, sum_range, ← FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) m (by simpa using hm')]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact Fintype.sum_equiv (Equiv.refl _) _ _ fun i ↦
    congrArg (· ^ m) (ZMod.natCast_zmod_val (n := n + 1) i)

/-- For a prime `p`, `1 ≤ a ≤ p - 1` and `k + m = p - 1`, we have `a^{-k} ≡ a^m (mod p ℤ_p)`. -/
theorem norm_inv_pow_sub_pow_le (p : ℕ) [Fact p.Prime] {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ p - 1)
    {k m : ℕ} (hkm : k + m = p - 1) :
    ‖((a : ℚ_[p]) ^ k)⁻¹ - (a : ℚ_[p]) ^ m‖ ≤ (p : ℝ)⁻¹ := by
  have hp := (Fact.out : p.Prime).two_le
  have hcop : Nat.Coprime a p := (Nat.coprime_of_lt_prime (by omega) (by omega) Fact.out).symm
  have hna : ‖(a : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hcop.symm
  have ha0 : (a : ℚ_[p]) ≠ 0 := by rw [← norm_ne_zero_iff, hna]; exact one_ne_zero
  have key : ((a : ℚ_[p]) ^ k)⁻¹ - (a : ℚ_[p]) ^ m =
      ((1 - (a : ℤ) ^ (p - 1) : ℤ) : ℚ_[p]) * ((a : ℚ_[p]) ^ k)⁻¹ := by
    rw [← hkm]; push_cast; field_simp; ring
  rw [key, norm_mul, norm_inv, norm_pow, hna, one_pow, inv_one, mul_one]
  have hdvd : (p : ℤ) ∣ 1 - (a : ℤ) ^ (p - 1) :=
    dvd_sub_comm.mp (Int.ModEq.pow_card_sub_one_eq_one Fact.out
      (Nat.isCoprime_iff_coprime.mpr hcop)).symm.dvd
  simpa using (Padic.norm_int_le_pow_iff_dvd (p := p) (1 - (a : ℤ) ^ (p - 1)) 1).mpr
    (by simpa using hdvd)

/-- For a prime `p` and `1 ≤ k < p - 1`, the power sum `∑_{a=1}^{p-1} a^{-k}` lies in `p ℤ_p`. -/
theorem norm_sum_inv_pow_le (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) (hk' : k < p - 1) :
    ‖∑ a ∈ Icc 1 (p - 1), ((a : ℚ_[p]) ^ k)⁻¹‖ ≤ (p : ℝ)⁻¹ := by
  set m := p - 1 - k
  have hkm : k + m = p - 1 := by omega
  have hT := (Padic.norm_int_le_pow_iff_dvd (p := p) _ 1).mpr
    (by simpa using prime_dvd_sum_Icc_pow p (m := m) (by omega) (by omega))
  rw [← sub_add_cancel (∑ a ∈ Icc 1 (p - 1), ((a : ℚ_[p]) ^ k)⁻¹)
    (∑ a ∈ Icc 1 (p - 1), (a : ℚ_[p]) ^ m), ← sum_sub_distrib]
  refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun a ha ↦ ?_
    rw [mem_Icc] at ha
    exact norm_inv_pow_sub_pow_le p ha.1 ha.2 hkm
  · simpa using hT

/-- **The power sum `∑_{a=1}^{p-1} a^{-4}`.** For a prime `p ≥ 7`, the sum
`∑_{a=1}^{p-1} a^{-4}` lies in `p ℤ_p`, i.e. its `p`-adic norm is at most `p⁻¹`. -/
@[zeta5irr "lem_local_power_sum"]
theorem norm_sum_inv_pow_four_le (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ‖∑ a ∈ Icc 1 (p - 1), ((a : ℚ_[p]) ^ 4)⁻¹‖ ≤ (p : ℝ)⁻¹ :=
  norm_sum_inv_pow_le p (by norm_num) (by omega)

end Zeta5Irr
