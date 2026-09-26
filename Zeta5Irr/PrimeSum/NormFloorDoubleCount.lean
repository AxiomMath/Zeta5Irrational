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
# A double-counting identity for `∑ ⌊2i/p⌋`

For every natural number `p` and every `h`,
`∑_{i=1}^{h-1} ⌊2i/p⌋ = ∑_{j=1}^{⌊2(h-1)/p⌋} (h - ⌈jp/2⌉)`.
Both sides count the lattice points `(i, j)` with `1 ≤ i ≤ h - 1`, `j ≥ 1` and `jp ≤ 2i`:
the left side sums over `i` first, the right side over `j` first.

## Main results

* `Nat.sum_Icc_two_mul_div_eq_sum_Icc`: the identity over `ℕ`, with floors and ceilings
  written as natural-number divisions.
* `Zeta5Irr.sum_floor_two_mul_div_eq_sum_sub_ceil`: the identity as stated in the source,
  with real floors and ceilings.

## Implementation notes

* The source assumes `p` prime and `h ≥ 2`; neither hypothesis is needed. For `p = 0` both
  sides vanish, since `⌊x / 0⌋ = 0` and the right-hand sum is then empty. The upper limit
  `h - 1` is a natural subtraction, so for `h ≤ 1` both sums are empty.
* The upper limit `⌊2(h-1)/p⌋` of the right-hand sum is a nonnegative integer, and is written
  as the natural-number quotient `2 (h - 1) / p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3: the inner asymptotics.
-/

@[expose] public section

namespace Nat

/-- Double counting of `{(i, j) : 1 ≤ i ≤ n, 1 ≤ j, j p ≤ 2 i}`, over `ℕ`:
`∑_{i=1}^{n} ⌊2i/p⌋ = ∑_{j=1}^{⌊2n/p⌋} (n + 1 - ⌈jp/2⌉)`, where `⌈m/2⌉ = (m + 1) / 2`. -/
theorem sum_Icc_two_mul_div_eq_sum_Icc {p : ℕ} (hp : 0 < p) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, 2 * i / p =
      ∑ j ∈ Finset.Icc 1 (2 * n / p), (n + 1 - (j * p + 1) / 2) := by
  have hL : ∀ i ∈ Finset.Icc 1 n, 2 * i / p =
      ((Finset.Icc 1 (2 * n / p)).filter (fun j => j * p ≤ 2 * i)).card := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have : (Finset.Icc 1 (2 * n / p)).filter (fun j => j * p ≤ 2 * i) =
        Finset.Icc 1 (2 * i / p) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, ← Nat.le_div_iff_mul_le hp]
      have : 2 * i / p ≤ 2 * n / p := Nat.div_le_div_right (by omega)
      omega
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  have hR : ∀ j ∈ Finset.Icc 1 (2 * n / p), n + 1 - (j * p + 1) / 2 =
      ((Finset.Icc 1 n).filter (fun i => j * p ≤ 2 * i)).card := by
    intro j hj
    rw [Finset.mem_Icc, Nat.le_div_iff_mul_le hp] at hj
    have : (Finset.Icc 1 n).filter (fun i => j * p ≤ 2 * i) =
        Finset.Icc ((j * p + 1) / 2) n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have : 1 ≤ j * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [this, Nat.card_Icc]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

end Nat

namespace Zeta5Irr

/-- The ceiling of `m / 2` for a natural number `m` is `(m + 1) / 2`. -/
lemma ceil_natCast_div_two (m : ℕ) : ⌈(m : ℝ) / 2⌉ = (((m + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k, (m + 1) / 2 = k := ⟨_, rfl⟩
  have h1 : (k : ℝ) * 2 < m + 2 := by exact_mod_cast (by omega : k * 2 < m + 2)
  have h2 : (m : ℝ) ≤ k * 2 := by exact_mod_cast (by omega : m ≤ k * 2)
  rw [hk, Int.ceil_eq_iff]
  push_cast
  constructor <;> linarith

/-- **Double counting for `∑ ⌊2i/p⌋`.** For all natural numbers `p` and `h`,
`∑_{i=1}^{h-1} ⌊2i/p⌋ = ∑_{j=1}^{⌊2(h-1)/p⌋} (h - ⌈jp/2⌉)`.
The source states this for `p` prime and `h ≥ 2`. -/
@[zeta5irr "lem_norm_floor_double_count"]
theorem sum_floor_two_mul_div_eq_sum_sub_ceil (p h : ℕ) :
    ∑ i ∈ Finset.Icc 1 (h - 1), ⌊(2 * i : ℝ) / p⌋ =
      ∑ j ∈ Finset.Icc 1 (2 * (h - 1) / p), ((h : ℤ) - ⌈(j * p : ℝ) / 2⌉) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hfl : ∀ i : ℕ, ⌊(2 * i : ℝ) / p⌋ = ((2 * i / p : ℕ) : ℤ) := fun i => by
    rw [show (2 * i : ℝ) = ((2 * i : ℕ) : ℝ) by push_cast; ring, Int.floor_div_natCast,
      Int.floor_natCast]
    norm_cast
  have hce : ∀ j ∈ Finset.Icc 1 (2 * (h - 1) / p),
      (h : ℤ) - ⌈(j * p : ℝ) / 2⌉ = ((h - 1 + 1 - (j * p + 1) / 2 : ℕ) : ℤ) := by
    intro j hj
    rw [Finset.mem_Icc, Nat.le_div_iff_mul_le hp] at hj
    rw [show (j * p : ℝ) = ((j * p : ℕ) : ℝ) by push_cast; ring, ceil_natCast_div_two]
    have : 1 ≤ j * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [Nat.cast_sub (by omega), Nat.sub_add_cancel (by omega)]
  simp only [hfl]
  rw [Finset.sum_congr rfl hce]
  exact_mod_cast Nat.sum_Icc_two_mul_div_eq_sum_Icc hp (h - 1)

end Zeta5Irr
