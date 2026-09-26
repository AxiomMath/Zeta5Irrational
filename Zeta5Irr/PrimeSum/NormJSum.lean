/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LimitingFunctions.J
public import Zeta5Irr.PrimeSum.NormFloorDoubleCount
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The floor sum `∑ ⌊2i/p⌋` and the inner limiting function

For a positive integer `p` and a natural number `h`, the floor sum `∑_{i=1}^{h-1} ⌊2i/p⌋`
is `p 𝒥(h/p)` up to an error of at most `h / p`, where `𝒥` is the inner limiting function.
Writing `m = ⌊2h/p⌋` and `k = ⌊2(h-1)/p⌋`, one has
`p 𝒥(h/p) = ∑_{j=1}^{m} (h - jp/2)`, while by double counting
`∑_{i=1}^{h-1} ⌊2i/p⌋ = ∑_{j=1}^{k} (h - ⌈jp/2⌉)`. Since `k ≤ m`, the difference is
`∑_{j ≤ k} (⌈jp/2⌉ - jp/2) + ∑_{k < j ≤ m} (h - jp/2)`, and every term lies in `[0, 1/2]`:
the first because `jp` is an integer, the second because `2h - 1 ≤ jp ≤ 2h` for `k < j ≤ m`.
So the error is at most `m / 2 ≤ h / p`.

With the parameters of the construction, `h = 37 n` and `K = 40 n`, and a prime
`p > K / M`, this gives the error bound `M`.

## Main results

* `Zeta5Irr.abs_sum_floor_two_mul_div_sub_mul_innerLimitingFunction_le`: for `p > 0`,
  `|∑_{i=1}^{h-1} ⌊2i/p⌋ - p 𝒥(h/p)| ≤ h / p`.
* `Zeta5Irr.abs_sum_floor_two_mul_div_sub_mul_innerLimitingFunction_le_of_lt`: the source's
  statement, `|∑_{i=1}^{h-1} ⌊2i/p⌋ - p 𝒥(h/p)| ≤ M` for `h = 37 n`, `K = 40 n` and `p > K/M`.

## Implementation notes

* The source assumes `M ≥ 40`, `K ≥ 200 M ^ 2`, `p` prime and `p ≤ K / 3`. Only `M > 0` and
  `K / M < p` are used: the bound `h / p ≤ M` follows from `h ≤ K < p M`. In particular `p`
  need not be odd, since `⌈jp/2⌉ - jp/2 ∈ {0, 1/2}` for every integer `jp`.
* The source compares `k` with `m` by cases on whether `p ∣ 2h`. When `jp = 2h - 1` for some
  `j` (for instance `p = 3`, `h = 2`) one has `k = m - 1` although `p ∤ 2h`, and the two
  closed forms differ by `1/2`. The argument here avoids the case split: it bounds the
  difference of the two sums termwise, which covers every case at once.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- Gauss's sum over `ℝ`: `∑_{j=1}^{m} j = m (m + 1) / 2`. -/
private lemma sum_Ioc_natCast_eq (m : ℕ) : ∑ j ∈ Ioc 0 m, (j : ℝ) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih]
    push_cast
    ring

/-- `p 𝒥(h/p) = ∑_{j=1}^{⌊2h/p⌋} (h - jp/2)`. -/
lemma mul_innerLimitingFunction_div_eq_sum {p : ℕ} (hp : 0 < p) (h : ℕ) :
    (p : ℝ) * innerLimitingFunction ((h : ℝ) / p) =
      ∑ j ∈ Ioc 0 (2 * h / p), ((h : ℝ) - j * p / 2) := by
  have hfl : ⌊2 * ((h : ℝ) / p)⌋ = ((2 * h / p : ℕ) : ℤ) := by
    rw [show 2 * ((h : ℝ) / p) = ((2 * h : ℕ) : ℝ) / p by push_cast; ring,
      Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  have hp' : (p : ℝ) ≠ 0 := by positivity
  generalize 2 * h / p = m at hfl ⊢
  rw [innerLimitingFunction_of_floor_eq hfl, sum_sub_distrib, ← sum_div, ← sum_mul,
    sum_Ioc_natCast_eq]
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, Int.cast_natCast]
  field_simp
  ring

/-- For `p > 0`, the floor sum `∑_{i=1}^{h-1} ⌊2i/p⌋` differs from `p 𝒥(h/p)` by at most
`h / p`. -/
theorem abs_sum_floor_two_mul_div_sub_mul_innerLimitingFunction_le {p : ℕ} (hp : 0 < p)
    (h : ℕ) :
    |∑ i ∈ Icc 1 (h - 1), (⌊(2 * i : ℝ) / p⌋ : ℝ) - p * innerLimitingFunction ((h : ℝ) / p)| ≤
      (h : ℝ) / p := by
  set k := 2 * (h - 1) / p with hk
  set m := 2 * h / p with hm
  have hkm : k ≤ m := Nat.div_le_div_right (by omega)
  have hS : ∑ i ∈ Icc 1 (h - 1), (⌊(2 * i : ℝ) / p⌋ : ℝ) =
      ∑ j ∈ Ioc 0 k, ((h : ℝ) - ⌈(j * p : ℝ) / 2⌉) := by
    have := sum_floor_two_mul_div_eq_sum_sub_ceil p h
    rw [show Icc 1 (2 * (h - 1) / p) = Ioc 0 k from Icc_add_one_left_eq_Ioc 0 k] at this
    exact_mod_cast this
  -- the difference, split at `k`
  have hsplit : (p : ℝ) * innerLimitingFunction ((h : ℝ) / p) -
      ∑ i ∈ Icc 1 (h - 1), (⌊(2 * i : ℝ) / p⌋ : ℝ) =
      ∑ j ∈ Ioc 0 k, ((⌈(j * p : ℝ) / 2⌉ : ℝ) - j * p / 2) +
        ∑ j ∈ Ioc k m, ((h : ℝ) - j * p / 2) := by
    rw [hS, mul_innerLimitingFunction_div_eq_sum hp, ← sum_Ioc_consecutive _ (Nat.zero_le k) hkm]
    have : ∑ j ∈ Ioc 0 k, ((h : ℝ) - j * p / 2) - ∑ j ∈ Ioc 0 k, ((h : ℝ) - ⌈(j * p : ℝ) / 2⌉) =
        ∑ j ∈ Ioc 0 k, ((⌈(j * p : ℝ) / 2⌉ : ℝ) - j * p / 2) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
    linarith
  -- the terms lie in `[0, 1/2]`
  have hceil : ∀ j : ℕ, 0 ≤ (⌈(j * p : ℝ) / 2⌉ : ℝ) - j * p / 2 ∧
      (⌈(j * p : ℝ) / 2⌉ : ℝ) - j * p / 2 ≤ 1 / 2 := by
    intro j
    rw [show (j * p : ℝ) = ((j * p : ℕ) : ℝ) by push_cast; ring, ceil_natCast_div_two]
    have h1 : j * p ≤ 2 * ((j * p + 1) / 2) := by omega
    have h2 : 2 * ((j * p + 1) / 2) ≤ j * p + 1 := by omega
    have h1' : ((j * p : ℕ) : ℝ) ≤ 2 * (((j * p + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : 2 * (((j * p + 1) / 2 : ℕ) : ℝ) ≤ ((j * p : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    rw [Nat.cast_mul] at h1' h2' ⊢
    rw [Int.cast_natCast]
    constructor <;> linarith
  have htop : ∀ j ∈ Ioc k m, 0 ≤ (h : ℝ) - j * p / 2 ∧ (h : ℝ) - j * p / 2 ≤ 1 / 2 := by
    intro j hj
    rw [mem_Ioc, hk, hm, Nat.div_lt_iff_lt_mul hp, Nat.le_div_iff_mul_le hp] at hj
    have h1 : j * p ≤ 2 * h := hj.2
    have h2 : 2 * h ≤ j * p + 1 := by
      have : 1 ≤ j * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by
        rintro rfl; simp at hj) (by omega))
      omega
    have h1' : ((j * p : ℕ) : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((2 * h : ℕ) : ℝ) ≤ ((j * p : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    push_cast at h1' h2'
    constructor <;> linarith
  have hA0 : 0 ≤ ∑ j ∈ Ioc 0 k, ((⌈(j * p : ℝ) / 2⌉ : ℝ) - j * p / 2) :=
    sum_nonneg fun j _ => (hceil j).1
  have hB0 : 0 ≤ ∑ j ∈ Ioc k m, ((h : ℝ) - j * p / 2) :=
    sum_nonneg fun j hj => (htop j hj).1
  have hA : ∑ j ∈ Ioc 0 k, ((⌈(j * p : ℝ) / 2⌉ : ℝ) - j * p / 2) ≤ k * (1 / 2) := by
    simpa using sum_le_card_nsmul (Ioc 0 k) _ (1 / 2 : ℝ) fun j _ => (hceil j).2
  have hB : ∑ j ∈ Ioc k m, ((h : ℝ) - j * p / 2) ≤ ((m - k : ℕ) : ℝ) * (1 / 2) := by
    simpa using sum_le_card_nsmul (Ioc k m) _ (1 / 2 : ℝ) fun j hj => (htop j hj).2
  have hmh : (m : ℝ) * p ≤ 2 * h := by exact_mod_cast Nat.div_mul_le_self (2 * h) p
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hmh' : (m : ℝ) / 2 ≤ (h : ℝ) / p := by
    rw [div_le_div_iff₀ (by norm_num) hp']
    linarith
  rw [Nat.cast_sub hkm] at hB
  rw [abs_sub_comm, abs_of_nonneg (by rw [hsplit]; positivity), hsplit]
  linarith

/-- **Lemma (the floor sum and `𝒥`).** Let `K = 40 n` be the pole bound and `h = 37 n` the
matrix order. For every `M > 0` and every `p > K / M`,
`|∑_{i=1}^{h-1} ⌊2i/p⌋ - p 𝒥(h/p)| ≤ M`.
The source states this for integers `M ≥ 40`, `K ≥ 200 M ^ 2` and primes `K / M < p ≤ K / 3`. -/
@[zeta5irr "lem_norm_J_sum"]
theorem abs_sum_floor_two_mul_div_sub_mul_innerLimitingFunction_le_of_lt {n p : ℕ} {M : ℝ}
    (hM : 0 < M) (hpK : (poleBound n : ℝ) / M < p) :
    |∑ i ∈ Icc 1 (matrixOrder n - 1), (⌊(2 * i : ℝ) / p⌋ : ℝ) -
        p * innerLimitingFunction ((matrixOrder n : ℝ) / p)| ≤ M := by
  have hp' : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hpK
  have hp : 0 < p := by exact_mod_cast hp'
  refine (abs_sum_floor_two_mul_div_sub_mul_innerLimitingFunction_le hp _).trans ?_
  have hhK : (matrixOrder n : ℝ) ≤ poleBound n := by
    simp only [matrixOrder, poleBound]
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [div_lt_iff₀ hM] at hpK
  rw [div_le_iff₀ hp']
  linarith

end Zeta5Irr
