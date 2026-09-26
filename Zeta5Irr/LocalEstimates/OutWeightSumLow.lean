/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutQ
public import Zeta5Irr.LocalEstimates.OutW0
public import Zeta5Irr.LocalEstimates.OutTp
public import Zeta5Irr.LocalEstimates.InExtraCount
public import Zeta5Irr.LocalEstimates.OutMK
public import Zeta5Irr.LocalEstimates.OutNLeMstar
public import Zeta5Irr.LocalEstimates.OutEllN
public import Zeta5Irr.LocalEstimates.OutTpCount
public import Zeta5Irr.LocalEstimates.OutCostRemoved
public import Zeta5Irr.LocalEstimates.OutCostUnremoved

/-!
# The total cost of the outer range when `K < 2p`

Let `p` be an odd prime with `p ≤ K < 2p` and `2N < p`. The entry valuations of the outer range
are `w_{0,i}` for the zero class, `0 ≤ i < deg Q_0`, and `w_{a,i}` for the ordinary classes
`1 ≤ a ≤ m°`, `0 ≤ i < deg Q_a`. Their total satisfies
`-2 ∑_{a=0}^{m°} ∑_{i=0}^{deg Q_a - 1} w_{a,i} = 7 (K - p) - 6 t_p + 1`.

Here `m_K = 1` and `m_N = 0`, so `v_K = K - p`, and the only pole `N < j ≤ K` divisible by `p`
is `j = p`; hence `deg Q_0 = 1` and the zero class costs `-2 w_{0,0} = 1`. For `1 ≤ a ≤ m°` put
`σ_a = 𝟙[a ≤ v_K] + 𝟙[p - a ≤ v_K]`; then `ℓ_K(a) = 2 + σ_a` and `deg Q_a = ℓ_K(a) - δ_a`, and
the cost of the class is `σ_a` if `a ≤ N` and `7 σ_a` otherwise. Summing,
`∑_{a=1}^{m°} σ_a = v_K` and `∑_{a=1}^{N} σ_a = t_p`.

## Main results

* `Zeta5Irr.natDegree_residuePoleProduct_add_outerDelta`: `deg Q_a + δ_a = ℓ_K(a)`.
* `Zeta5Irr.residuePoleIndices_zero`: for `N < p ≤ K < 2p`, the only far pole in the zero class
  is `p`.
* `Zeta5Irr.neg_two_mul_sum_outerWeight_of_lt_two_mul`: the total cost identity.

## Implementation notes

* The double sum over `0 ≤ a ≤ m°` is written as the zero-class sum (with the weights
  `w_{0,i} = Zeta5Irr.outerWeightZero m_K m_N i`) plus the sum over `1 ≤ a ≤ m°` (with the
  weights `w_{a,i} = Zeta5Irr.outerWeight`), since the source defines the two families
  separately. The degree `deg Q_a` is the `natDegree` of `Q_a` over any nontrivial commutative
  ring.
* Only `p` odd, `p ≤ K < 2p` and `2N < p` are used; the source's hypotheses `p` prime, `p ≥ 7`,
  `K ∈ 40 ℤ_{>0}` with `N = 3K/40`, `p² > 2K` and `5N ≤ 2p - 2` are not needed, and `N`, `K`
  are arbitrary natural numbers.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `2N < p`, `N ≤ K` and `1 ≤ a ≤ m°`, `deg Q_a + δ_a = ℓ_K(a)`. -/
theorem natDegree_residuePoleProduct_add_outerDelta (R : Type*) [CommRing R] [Nontrivial R]
    {p N K a : ℕ} (hN : 2 * N < p) (hNK : N ≤ K) (ha₁ : 1 ≤ a) (ha₂ : a ≤ mStar p) :
    (residuePoleProduct R p a N K).natDegree + outerDelta N a = ellA p K a := by
  rw [natDegree_residuePoleProduct, ← ellA_eq_outerDelta hN ha₁ ha₂]
  exact_mod_cast card_residuePoleIndices_add_ellA p a hNK

/-- If `N < p ≤ K < 2p`, the only `N < j ≤ K` with `j ≡ 0 (mod p)` is `j = p`. -/
theorem residuePoleIndices_zero {p N K : ℕ} (hN : N < p) (hpK : p ≤ K) (hK : K < 2 * p) :
    residuePoleIndices p 0 N K = {p} := by
  ext j
  simp only [mem_residuePoleIndices, Int.cast_zero, neg_zero, or_self, mem_singleton,
    ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, c, rfl⟩
    have hc1 : c < 2 := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
    interval_cases c <;> omega
  · rintro rfl
    exact ⟨⟨hN, hpK⟩, dvd_rfl⟩

/-- **The total cost when `K < 2p`.** For `p` odd with `p ≤ K < 2p` and `2N < p`,
`-2 ∑_{a=0}^{m°} ∑_{i=0}^{deg Q_a - 1} w_{a,i} = 7 (K - p) - 6 t_p + 1`, the class `a = 0`
carrying the weights `w_{0,i}` and the classes `1 ≤ a ≤ m°` the weights `w_{a,i}`. -/
@[zeta5irr "lem_out_weight_sum_low"]
theorem neg_two_mul_sum_outerWeight_of_lt_two_mul (R : Type*) [CommRing R] [Nontrivial R]
    {p N K : ℕ} (hp : Odd p) (hpK : p ≤ K) (hK : K < 2 * p) (hN : 2 * N < p) :
    -2 * (∑ i ∈ range (residuePoleProduct R p 0 N K).natDegree,
          outerWeightZero (mA p K) (mA p N) i +
        ∑ a ∈ Icc 1 (mStar p), ∑ i ∈ range (residuePoleProduct R p a N K).natDegree,
          outerWeight p K N a i) =
      7 * ((K : ℚ) - p) - 6 * smallClassCount p N K + 1 := by
  have hp0 : 0 < p := hp.pos
  have hmK : mA p K = 1 := mA_eq_one_of_lt_two_mul hpK hK
  have hmN : mA p N = 0 := mA_eq_zero_of_two_mul_lt hN
  have hvK : (vA p K : ℚ) = K - p := by
    have := mul_mA_add_vA p K
    rw [hmK] at this
    rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : vA p K + p = K)
  -- the zero class
  have h0 : ∑ i ∈ range (residuePoleProduct R p 0 N K).natDegree,
      outerWeightZero (mA p K) (mA p N) i = -1 / 2 := by
    rw [natDegree_residuePoleProduct, residuePoleIndices_zero (by omega) hpK hK, card_singleton,
      sum_range_one, outerWeightZero_of_sub_eq_one (by rw [hmK, hmN])]
  -- an ordinary class
  set σ : ℕ → ℕ := fun a ↦ (if a ≤ vA p K then 1 else 0) + (if p - a ≤ vA p K then 1 else 0)
    with hσ
  have hcls : ∀ a ∈ Icc 1 (mStar p),
      -2 * ∑ i ∈ range (residuePoleProduct R p a N K).natDegree, outerWeight p K N a i =
        7 * (σ a : ℚ) - 6 * (if a ≤ N then (σ a : ℚ) else 0) := by
    intro a ha
    rw [mem_Icc] at ha
    have hell : ellA p K a = 2 + σ a := by
      rw [ellA_eq_two_mul_mA_add ha.1 ha.2, hmK]; simp only [hσ]; ring
    have hσ2 : σ a ≤ 2 := by simp only [hσ]; split_ifs <;> omega
    have hdeg := natDegree_residuePoleProduct_add_outerDelta R (K := K) hN (by omega) ha.1 ha.2
    by_cases haN : a ≤ N
    · have hδ : outerDelta (N : ℤ) (a : ℤ) = 1 := outerDelta_of_le (by exact_mod_cast haN)
      have hδ' : outerDelta N a = 1 := hδ
      rw [hδ'] at hdeg
      simp only [haN, ↓reduceIte]
      rw [show (residuePoleProduct R p a N K).natDegree = ellA p K a - 1 by omega,
        neg_two_mul_sum_outerWeight hδ (by omega) (by omega), hell]
      generalize σ a = s at hσ2 ⊢
      interval_cases s <;> norm_num
    · have hδ : outerDelta (N : ℤ) (a : ℤ) = 0 :=
        outerDelta_of_lt (by exact_mod_cast not_le.1 haN)
      have hδ' : outerDelta N a = 0 := hδ
      rw [hδ'] at hdeg
      simp only [haN, ↓reduceIte]
      rw [show (residuePoleProduct R p a N K).natDegree = ellA p K a by omega,
        neg_two_mul_sum_outerWeight_of_outerDelta_eq_zero hδ (by omega) (by omega), hell]
      push_cast; ring
  have hsum (S : Finset ℕ) : ∑ a ∈ S, (σ a : ℚ) =
      (#{a ∈ S | a ≤ vA p K} + #{a ∈ S | p - a ≤ vA p K} : ℕ) := by
    simp only [hσ]; push_cast; rw [sum_add_distrib, sum_boole, sum_boole]
  rw [mul_add, h0, mul_sum, sum_congr rfl hcls, sum_sub_distrib, ← mul_sum, ← mul_sum,
    ← sum_filter, filter_Icc_one_mStar_le_eq hN, hsum, hsum, card_le_vA_add_card_sub_le_vA hp,
    card_filter_le_vA_add_card_filter_sub_le_vA hp0, hvK]
  ring

end Zeta5Irr
