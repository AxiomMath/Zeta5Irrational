/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutWeightSumLow

/-!
# The total cost of the outer range when `2p ≤ K < 3p`

Let `p` be an odd prime with `2p ≤ K < 3p` and `2N < p`. The entry valuations of the outer range
are `w_{0,i}` for the zero class, `0 ≤ i < deg Q_0`, and `w_{a,i}` for the ordinary classes
`1 ≤ a ≤ m°`, `0 ≤ i < deg Q_a`. Their total satisfies
`-2 ∑_{a=0}^{m°} ∑_{i=0}^{deg Q_a - 1} w_{a,i} = 7 (K - p) - 3 - 12 N - 5 t_p`.

Here `m_K = 2` and `m_N = 0`, so `v_K = K - 2p`, and the poles `N < j ≤ K` divisible by `p`
are `j = p` and `j = 2p`; hence `deg Q_0 = 2` and the zero class costs
`-2 (w_{0,0} + w_{0,1}) = 4`. For `1 ≤ a ≤ m°` put `σ_a = 𝟙[a ≤ v_K] + 𝟙[p - a ≤ v_K]`; then
`ℓ_K(a) = 4 + σ_a` and `deg Q_a = ℓ_K(a) - δ_a`, and the cost of the class is `2 + 2 σ_a` if
`a ≤ N` and `14 + 7 σ_a` otherwise. Summing, with `∑_{a=1}^{m°} σ_a = v_K`,
`∑_{a=1}^{N} σ_a = t_p` and `2 m° = p - 1`, gives the identity.

## Main results

* `Zeta5Irr.residuePoleIndices_zero_of_two_mul_le`: for `N < p` and `2p ≤ K < 3p`, the far
  poles in the zero class are `p` and `2p`.
* `Zeta5Irr.neg_two_mul_sum_outerWeight_of_two_mul_le`: the total cost identity.

## Implementation notes

* The double sum over `0 ≤ a ≤ m°` is written as the zero-class sum (with the weights
  `w_{0,i} = Zeta5Irr.outerWeightZero m_K m_N i`) plus the sum over `1 ≤ a ≤ m°` (with the
  weights `w_{a,i} = Zeta5Irr.outerWeight`), since the source defines the two families
  separately. The degree `deg Q_a` is the `natDegree` of `Q_a` over any nontrivial commutative
  ring.
* Only `p` odd, `2p ≤ K < 3p` and `2N < p` are used; the source's hypotheses `p` prime,
  `p ≥ 7`, `K ∈ 40 ℤ_{>0}` with `N = 3K/40`, `p² > 2K` and `5N ≤ 2p - 2` are not needed, and
  `N`, `K` are arbitrary natural numbers.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- If `N < p` and `2p ≤ K < 3p`, the `N < j ≤ K` with `j ≡ 0 (mod p)` are `j = p` and
`j = 2p`. -/
theorem residuePoleIndices_zero_of_two_mul_le {p N K : ℕ} (hN : N < p) (hpK : 2 * p ≤ K)
    (hK : K < 3 * p) : residuePoleIndices p 0 N K = {p, 2 * p} := by
  ext j
  simp only [mem_residuePoleIndices, Int.cast_zero, neg_zero, or_self, mem_insert,
    mem_singleton, ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, c, rfl⟩
    have hc1 : c < 3 := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
    interval_cases c <;> omega
  · rintro (rfl | rfl)
    · exact ⟨⟨hN, by omega⟩, dvd_rfl⟩
    · exact ⟨⟨by omega, hpK⟩, dvd_mul_left p 2⟩

/-- For `2p ≤ K < 3p`, `2N < p` and `1 ≤ a ≤ m°`, the class `a` costs `2 + 2 σ_a` if `a ≤ N`
and `14 + 7 σ_a` otherwise, where `σ_a = 𝟙[a ≤ v_K] + 𝟙[p - a ≤ v_K]`. -/
theorem neg_two_mul_sum_outerWeight_class_of_two_mul_le (R : Type*) [CommRing R] [Nontrivial R]
    {p N K a : ℕ} (hpK : 2 * p ≤ K) (hK : K < 3 * p) (hN : 2 * N < p) (ha₁ : 1 ≤ a)
    (ha₂ : a ≤ mStar p) :
    -2 * ∑ i ∈ range (residuePoleProduct R p a N K).natDegree, outerWeight p K N a i =
      (14 + 7 * (((if a ≤ vA p K then 1 else 0) + (if p - a ≤ vA p K then 1 else 0) : ℕ) : ℚ)) -
        (if a ≤ N then
          12 + 5 * (((if a ≤ vA p K then 1 else 0) + (if p - a ≤ vA p K then 1 else 0) : ℕ) : ℚ)
        else 0) := by
  set σ : ℕ := (if a ≤ vA p K then 1 else 0) + (if p - a ≤ vA p K then 1 else 0) with hσ
  have hell : ellA p K a = 4 + σ := by
    rw [ellA_eq_two_mul_mA_add ha₁ ha₂, mA_eq_two_of_two_mul_le hpK hK, hσ]
    ring
  have hσ₂ : σ ≤ 2 := by
    rw [hσ]
    split_ifs <;> omega
  have hdeg := natDegree_residuePoleProduct_add_outerDelta R (K := K) hN (by omega) ha₁ ha₂
  by_cases haN : a ≤ N
  · have hδ : outerDelta (N : ℤ) (a : ℤ) = 1 := outerDelta_of_le (by exact_mod_cast haN)
    rw [show outerDelta N a = 1 from hδ] at hdeg
    simp only [haN, ↓reduceIte]
    rw [show (residuePoleProduct R p a N K).natDegree = ellA p K a - 1 by omega,
      neg_two_mul_sum_outerWeight hδ (by omega) (by omega), hell]
    generalize σ = s at hσ₂ ⊢
    interval_cases s <;> norm_num
  · have hδ : outerDelta (N : ℤ) (a : ℤ) = 0 :=
      outerDelta_of_lt (by exact_mod_cast not_le.1 haN)
    rw [show outerDelta N a = 0 from hδ] at hdeg
    simp only [haN, ↓reduceIte]
    rw [show (residuePoleProduct R p a N K).natDegree = ellA p K a by omega,
      neg_two_mul_sum_outerWeight_of_outerDelta_eq_zero hδ (by omega) (by omega), hell]
    push_cast
    ring

/-- **The total cost when `2p ≤ K < 3p`.** For `p` odd with `2p ≤ K < 3p` and `2N < p`,
`-2 ∑_{a=0}^{m°} ∑_{i=0}^{deg Q_a - 1} w_{a,i} = 7 (K - p) - 3 - 12 N - 5 t_p`, the class
`a = 0` carrying the weights `w_{0,i}` and the classes `1 ≤ a ≤ m°` the weights `w_{a,i}`. -/
@[zeta5irr "lem_out_weight_sum_high"]
theorem neg_two_mul_sum_outerWeight_of_two_mul_le (R : Type*) [CommRing R] [Nontrivial R]
    {p N K : ℕ} (hp : Odd p) (hpK : 2 * p ≤ K) (hK : K < 3 * p) (hN : 2 * N < p) :
    -2 * (∑ i ∈ range (residuePoleProduct R p 0 N K).natDegree,
          outerWeightZero (mA p K) (mA p N) i +
        ∑ a ∈ Icc 1 (mStar p), ∑ i ∈ range (residuePoleProduct R p a N K).natDegree,
          outerWeight p K N a i) =
      7 * ((K : ℚ) - p) - 3 - 12 * N - 5 * smallClassCount p N K := by
  have hp0 : 0 < p := hp.pos
  have hmK : mA p K = 2 := mA_eq_two_of_two_mul_le hpK hK
  have hmN : mA p N = 0 := mA_eq_zero_of_two_mul_lt hN
  have hvK : (vA p K : ℚ) = K - 2 * p := by
    have := mul_mA_add_vA p K
    rw [hmK] at this
    rw [eq_sub_iff_add_eq]
    exact_mod_cast (by omega : vA p K + 2 * p = K)
  have hmS : 2 * (mStar p : ℚ) = p - 1 := by
    rw [eq_sub_iff_add_eq]
    exact_mod_cast two_mul_mStar_add_one hp
  have h0 : ∑ i ∈ range (residuePoleProduct R p 0 N K).natDegree,
      outerWeightZero (mA p K) (mA p N) i = -2 := by
    rw [natDegree_residuePoleProduct, residuePoleIndices_zero_of_two_mul_le (by omega) hpK hK,
      card_pair (by omega), sum_range_succ, sum_range_one,
      outerWeightZero_of_sub_eq_two (by rw [hmK, hmN]),
      outerWeightZero_of_sub_eq_two (by rw [hmK, hmN])]
    norm_num
  set σ : ℕ → ℕ := fun a ↦ (if a ≤ vA p K then 1 else 0) + (if p - a ≤ vA p K then 1 else 0)
    with hσ
  have hcls : ∀ a ∈ Icc 1 (mStar p),
      -2 * ∑ i ∈ range (residuePoleProduct R p a N K).natDegree, outerWeight p K N a i =
        (14 + 7 * (σ a : ℚ)) - (if a ≤ N then 12 + 5 * (σ a : ℚ) else 0) := fun a ha ↦
    neg_two_mul_sum_outerWeight_class_of_two_mul_le R hpK hK hN (mem_Icc.1 ha).1 (mem_Icc.1 ha).2
  have hsum (S : Finset ℕ) : ∑ a ∈ S, (σ a : ℚ) =
      (#{a ∈ S | a ≤ vA p K} + #{a ∈ S | p - a ≤ vA p K} : ℕ) := by
    simp only [hσ]
    push_cast
    rw [sum_add_distrib, sum_boole, sum_boole]
  rw [mul_add, h0, mul_sum, sum_congr rfl hcls, sum_sub_distrib, ← sum_filter,
    filter_Icc_one_mStar_le_eq hN, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hsum,
    hsum, card_le_vA_add_card_sub_le_vA hp, card_filter_le_vA_add_card_filter_sub_le_vA hp0,
    hvK, sum_const, sum_const, Nat.card_Icc, Nat.card_Icc]
  simp only [add_tsub_cancel_right, nsmul_eq_mul]
  linear_combination 7 * hmS

end Zeta5Irr
