/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutWeightSumLow
public import Zeta5Irr.LocalEstimates.OutU
public import Zeta5Irr.LocalEstimates.OutBothCount
public import Zeta5Irr.LocalEstimates.OutZerocountRemoved
public import Zeta5Irr.LocalEstimates.OutZerocountUnremoved

/-!
# The number of vanishing entry valuations in the outer range when `K < 2p`

Let `p` be an odd prime with `p ≤ K < 2p` and `2N < p`. Among the entry valuations of the outer
range — `w_{0,i}` for the zero class, `0 ≤ i < deg Q_0`, and `w_{a,i}` for the ordinary classes
`1 ≤ a ≤ m°`, `0 ≤ i < deg Q_a` — exactly `p - 1 - N + u` vanish.

Here `m_K = 1` and `m_N = 0`, so `v_K = K - p`, `deg Q_0 = 1` and the single weight of the zero
class is `w_{0,0} = -1/2 ≠ 0`. For `1 ≤ a ≤ m°` put `σ_a = 𝟙[a ≤ v_K] + 𝟙[p - a ≤ v_K]`, so that
`ℓ_K(a) = 2 + σ_a` and `deg Q_a = ℓ_K(a) - δ_a`. A removed class (`a ≤ N`) has
`⌊ℓ_K(a)/2⌋ = 1 + 𝟙[σ_a = 2]` vanishing weights, an unremoved class has `2`. Summing, the count
is `N + u + 2 (m° - N) = p - 1 - N + u`, using `#{a ≤ N : σ_a = 2} = u` and `2 m° = p - 1`.

## Main results

* `Zeta5Irr.card_filter_outerWeight_eq_zero_of_lt_two_mul`: the zero count identity.

## Implementation notes

* As in `Zeta5Irr.neg_two_mul_sum_outerWeight_of_lt_two_mul`, the count over `0 ≤ a ≤ m°` is
  written as the zero-class count (weights `w_{0,i} = Zeta5Irr.outerWeightZero m_K m_N i`) plus
  the sum over `1 ≤ a ≤ m°` of the class counts (weights `w_{a,i} = Zeta5Irr.outerWeight`),
  and `deg Q_a` is the `natDegree` of `Q_a` over any nontrivial commutative ring.
* Only `p` odd, `p ≤ K < 2p` and `2N < p` are used; the source's hypotheses `p` prime, `p ≥ 7`,
  `K ∈ 40 ℤ_{>0}` with `N = 3K/40`, `p² > 2K` and `5N ≤ 2p - 2` are not needed, and `N`, `K`
  are arbitrary natural numbers. The right-hand side `p - 1 - N + u` is computed in `ℕ`, which
  is harmless since `N < p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- **The zero count when `K < 2p`.** For `p` odd with `p ≤ K < 2p` and `2N < p`, the number of
pairs `(a, i)`, `0 ≤ a ≤ m°`, `0 ≤ i < deg Q_a`, with `w_{a,i} = 0` is `p - 1 - N + u`; the class
`a = 0` carries the weights `w_{0,i}` and the classes `1 ≤ a ≤ m°` the weights `w_{a,i}`. -/
@[zeta5irr "lem_out_zerocount_low"]
theorem card_filter_outerWeight_eq_zero_of_lt_two_mul (R : Type*) [CommRing R] [Nontrivial R]
    {p N K : ℕ} (hp : Odd p) (hpK : p ≤ K) (hK : K < 2 * p) (hN : 2 * N < p) :
    #{i ∈ range (residuePoleProduct R p 0 N K).natDegree |
        outerWeightZero (mA p K) (mA p N) i = 0} +
      ∑ a ∈ Icc 1 (mStar p),
        #{i ∈ range (residuePoleProduct R p a N K).natDegree | outerWeight p K N a i = 0} =
      p - 1 - N + overlapCount p N K := by
  have hmK : mA p K = 1 := mA_eq_one_of_lt_two_mul hpK hK
  have hmN : mA p N = 0 := mA_eq_zero_of_two_mul_lt hN
  -- the zero class
  have h0 : #{i ∈ range (residuePoleProduct R p 0 N K).natDegree |
      outerWeightZero (mA p K) (mA p N) i = 0} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun i _ ↦ outerWeightZero_ne_zero_of_sub_eq_one (by rw [hmK, hmN]) i
  -- an ordinary class
  set P : ℕ → Prop := fun a ↦ a ≤ vA p K ∧ p - a ≤ vA p K with hP
  have hcls : ∀ a ∈ Icc 1 (mStar p),
      #{i ∈ range (residuePoleProduct R p a N K).natDegree | outerWeight p K N a i = 0} +
          (if a ≤ N then 1 else 0) =
        2 + (if a ∈ Icc 1 N ∧ P a then 1 else 0) := by
    intro a ha
    rw [mem_Icc] at ha
    have hell : ellA p K a = 2 + (if a ≤ vA p K then 1 else 0) +
        (if p - a ≤ vA p K then 1 else 0) := by
      rw [ellA_eq_two_mul_mA_add ha.1 ha.2, hmK]
    have hdeg := natDegree_residuePoleProduct_add_outerDelta R (K := K) hN (by omega) ha.1 ha.2
    by_cases haN : a ≤ N
    · have hδ : outerDelta (N : ℤ) (a : ℤ) = 1 := outerDelta_of_le (by exact_mod_cast haN)
      have hδ' : outerDelta N a = 1 := hδ
      rw [hδ'] at hdeg
      rw [show (residuePoleProduct R p a N K).natDegree = ellA p K a - 1 by omega,
        card_filter_outerWeight_eq_zero hδ, hell]
      simp only [hP, mem_Icc, haN, ha.1, true_and, ite_true]
      split_ifs <;> omega
    · have hδ : outerDelta (N : ℤ) (a : ℤ) = 0 :=
        outerDelta_of_lt (by exact_mod_cast not_le.1 haN)
      have hδ' : outerDelta N a = 0 := hδ
      rw [hδ'] at hdeg
      have h2 : 2 ≤ ellA p K a := by rw [hell]; omega
      have h9 : ellA p K a ≤ 9 := by rw [hell]; split_ifs <;> omega
      rw [show (residuePoleProduct R p a N K).natDegree = ellA p K a by omega,
        card_filter_outerWeight_eq_zero_of_outerDelta_eq_zero hδ h2 h9]
      simp [mem_Icc, haN]
  have hsum := sum_congr rfl hcls
  rw [sum_add_distrib, sum_add_distrib, ← card_filter, ← card_filter, sum_const, smul_eq_mul,
    Nat.card_Icc] at hsum
  have hfiltP : {a ∈ Icc 1 (mStar p) | a ∈ Icc 1 N ∧ P a} = {a ∈ Icc 1 N | P a} := by
    have := le_mStar_of_two_mul_lt hN
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [filter_Icc_one_mStar_le_eq hN, hfiltP, Nat.card_Icc,
    card_filter_le_vA_and_sub_le_vA hN] at hsum
  have := two_mul_mStar_add_one hp
  rw [h0]
  omega

end Zeta5Irr
