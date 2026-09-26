/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsOut
public import Zeta5Irr.LocalEstimates.OutEntryInt
public import Zeta5Irr.LocalEstimates.OutResidVal
public import Zeta5Irr.LocalEstimates.OutZeroVal

/-!
# The outer range: the entry bound

Let `p ≥ 7` be a prime, fix the parameters `N = 3 n` and `K = 40 n`, and let `0 ≤ a, c ≤ m°`,
`0 ≤ i < deg Q_a` and `0 ≤ j < deg Q_c`. The entry `Φ₀(P_a q_{a,i}, P_c q_{c,j})` of the
integral part of the outer form on the separating basis satisfies
`v_p^G(Φ₀(P_a q_{a,i}, P_c q_{c,j})) ≥ w_{a,i} + w_{c,j}`.

All the weights are nonpositive, so an entry in `ℤ_p[X]` satisfies the bound; this covers the
cross entries `a ≠ c` and the entries with `a = c ≥ 1` and `max(i, j) ≥ ℓ_K(a) - 2`. The
class-`0` entries are bounded directly. For `a = c ≥ 1` and `i, j < ℓ_K(a) - 2`, write
`x = i + 3 δ_a - (ℓ_K(a) + 4) / 2` and `y = j + 3 δ_a - (ℓ_K(a) + 4) / 2`; the residue
valuation gives `v_p^G ≥ min(0, x + y) ≥ min(0, x) + min(0, y) = w_{a,i} + w_{a,j}`.

## Main definitions

* `Zeta5Irr.outerLocalWeight`: the weight `w_{a,i}` for every `0 ≤ a ≤ m°`, equal to `w_{0,i}`
  at `a = 0` and to the ordinary weight `w_{a,i}` otherwise.

## Main results

* `Zeta5Irr.card_residuePoleIndices_zero`: `deg Q_0 = m_K - m_N`, in counting form.
* `Zeta5Irr.outerLocalWeight_add_le_vpG_outerIntegralForm`: the entry bound
  `v_p^G(Φ₀(P_a q_{a,i}, P_c q_{c,j})) ≥ w_{a,i} + w_{c,j}`.

## Implementation notes

* The two families of weights `w_{0,i}` and `w_{a,i}` (`a ≥ 1`) are packaged into the single
  function `Zeta5Irr.outerLocalWeight`, just as `Zeta5Irr.outerLocalPoly` packages the local
  polynomials `q_{0,i}` and `q_{a,i}`.
* The bound is stated in `WithTop ℚ`, the Gauss valuation being mapped along `ℤ → ℚ`,
  because the weights are rational.
* The degree `deg Q_a` is written as the number of far poles `N < j ≤ K` with `j ≡ ±a (mod p)`,
  which is `deg Q_a` by `Zeta5Irr.natDegree_residuePoleProduct`; this is the row count of the
  outer coefficient matrix. The bound on `i` and `j` is only used when `a = c = 0`.
* The source's hypothesis `5 N ≤ 2 p - 2` is not used, so the result is stated without it;
  `K ∈ 40 ℤ_{>0}` is built in through `K = 40 n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10: the outer range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- The weight `w_{a,i}` of the row `(a, i)` of the outer range: the class-`0` weight
`w_{0,i} = Zeta5Irr.outerWeightZero m_K m_N i` at `a = 0`, and the ordinary weight
`w_{a,i} = Zeta5Irr.outerWeight` otherwise. -/
def outerLocalWeight (p N K : ℕ) (a : ℤ) (i : ℕ) : ℚ :=
  if a = 0 then outerWeightZero (mA p K) (mA p N) i else outerWeight p K N a i

/-- At `a = 0` the weight is the class-`0` weight `w_{0,i}`. -/
@[simp]
theorem outerLocalWeight_zero (p N K i : ℕ) :
    outerLocalWeight p N K 0 i = outerWeightZero (mA p K) (mA p N) i := by
  simp [outerLocalWeight]

/-- At `a ≠ 0` the weight is the ordinary weight `w_{a,i}`. -/
theorem outerLocalWeight_of_ne_zero {p N K : ℕ} {a : ℤ} (ha : a ≠ 0) (i : ℕ) :
    outerLocalWeight p N K a i = outerWeight p K N a i := by
  simp [outerLocalWeight, ha]

/-- If `m_K - m_N ≤ 2`, the class-`0` weights `w_{0,i}`, `i < m_K - m_N`, are nonpositive. -/
theorem outerWeightZero_nonpos {mK mN i : ℕ} (h : mK - mN ≤ 2) (hi : i < mK - mN) :
    outerWeightZero mK mN i ≤ 0 := by
  unfold outerWeightZero
  split_ifs
  · norm_num
  · have : (i : ℚ) ≤ 1 := by exact_mod_cast (by omega : i ≤ 1)
    linarith

/-- The number of far poles `N < j ≤ K` in the class `0` modulo `p` is `m_K - m_N`; that is,
`deg Q_0 = m_K - m_N`. -/
theorem card_residuePoleIndices_zero (p : ℕ) {N K : ℕ} (h : N ≤ K) :
    #(residuePoleIndices p 0 N K) = mA p K - mA p N := by
  have hS : residuePoleIndices p 0 N K =
      {x ∈ Ioc 0 K | p ∣ x} \ {x ∈ Ioc 0 N | p ∣ x} := by
    ext j
    simp only [mem_residuePoleIndices, Int.cast_zero, neg_zero, or_self,
      ZMod.natCast_eq_zero_iff, mem_sdiff, mem_filter, mem_Ioc]
    omega
  rw [hS, card_sdiff_of_subset, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]
  intro j
  simp only [mem_filter, mem_Ioc]
  omega

variable {p : ℕ} [Fact p.Prime]

/-- **The outer entry bound.** Let `p ≥ 7` be a prime with `p ≤ K < 3 p`, `2 K < p²` and
`2 N < p`, where `N = 3 n` and `K = 40 n`, let `0 ≤ a, c ≤ m°`, `i < deg Q_a` and
`j < deg Q_c`. Then `v_p^G(Φ₀(P_a q_{a,i}, P_c q_{c,j})) ≥ w_{a,i} + w_{c,j}`. -/
@[zeta5irr "lem_out_entry_val"]
theorem outerLocalWeight_add_le_vpG_outerIntegralForm (hp7 : 7 ≤ p) {n : ℕ}
    (hpK : p ≤ poleBound n) (hK3 : poleBound n < 3 * p) (hK2 : 2 * poleBound n < p ^ 2)
    (hN : 2 * innerDegree n < p) {a c : ℕ} (ha : a ≤ mStar p) (hc : c ≤ mStar p) {i j : ℕ}
    (hi : i < #(residuePoleIndices p a (innerDegree n) (poleBound n)))
    (hj : j < #(residuePoleIndices p c (innerDegree n) (poleBound n))) :
    ((outerLocalWeight p (innerDegree n) (poleBound n) a i +
        outerLocalWeight p (innerDegree n) (poleBound n) c j : ℚ) : WithTop ℚ) ≤
      (vpG (outerIntegralForm p n
        (complClassFactor ℚ p (a : ℤ) (innerDegree n) (poleBound n) *
          outerLocalPoly ℚ p (poleBound n) (a : ℤ) i)
        (complClassFactor ℚ p (c : ℤ) (innerDegree n) (poleBound n) *
          outerLocalPoly ℚ p (poleBound n) (c : ℤ) j))).map ((↑) : ℤ → ℚ) := by
  have hNK : innerDegree n ≤ poleBound n := by
    simp only [innerDegree, poleBound]; omega
  have hmN : mA p (innerDegree n) = 0 := mA_eq_zero_of_two_mul_lt (by omega)
  have hmK : mA p (poleBound n) < 3 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  -- all the weights in range are nonpositive
  have hw (e k : ℕ) (hk : k < #(residuePoleIndices p e (innerDegree n) (poleBound n))) :
      outerLocalWeight p (innerDegree n) (poleBound n) e k ≤ 0 := by
    rcases eq_or_ne e 0 with rfl | he
    · rw [Nat.cast_zero, outerLocalWeight_zero]
      rw [Nat.cast_zero, card_residuePoleIndices_zero p hNK] at hk
      exact outerWeightZero_nonpos (by omega) hk
    · rw [outerLocalWeight_of_ne_zero (by exact_mod_cast he)]
      exact outerWeight_nonpos _ _ _ _ _
  have hsum := add_nonpos (hw a i hi) (hw c j hj)
  -- an entry in `ℤ_p[X]` satisfies the bound
  have hint {T : ℚ_[p][X]} (hT : T ∈ lifts (PadicInt.Coe.ringHom (p := p))) :
      ((outerLocalWeight p (innerDegree n) (poleBound n) a i +
        outerLocalWeight p (innerDegree n) (poleBound n) c j : ℚ) : WithTop ℚ) ≤
        (vpG T).map ((↑) : ℤ → ℚ) :=
    coe_le_map_intCast_of_le (m := 0) (by simpa using hsum) (vpG_nonneg_of_mem_lifts hT)
  rcases ne_or_eq a c with hac | rfl
  · exact hint (outerIntegralForm_complClassFactor_mul_outerLocalPoly_mem_lifts hp7 n ha hc
      hac i j)
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [Nat.cast_zero, card_residuePoleIndices_zero p hNK] at hi hj
    simp only [Nat.cast_zero, outerLocalWeight_zero, outerLocalPoly_zero]
    exact outerWeightZero_add_le_vpG_outerIntegralForm hp7 hK3 (by omega) hi hj
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
  have ha0' : (a : ℤ) ≠ 0 := by exact_mod_cast ha0
  simp only [outerLocalPoly_of_ne_zero ha0']
  by_cases hij : ellA p (poleBound n) a - 2 ≤ max i j
  · exact hint (outerIntegralForm_complClassFactor_mul_outerBasis_mem_lifts hp7 hpK hN ha1 ha
      hij)
  push Not at hij
  have hi' : i < ellA p (poleBound n) a - 2 := lt_of_le_of_lt (le_max_left _ _) hij
  have hj' : j < ellA p (poleBound n) a - 2 := lt_of_le_of_lt (le_max_right _ _) hij
  refine coe_le_map_intCast_of_le ?_
    (min_le_vpG_outerIntegralForm_complClassFactor_mul_outerBasis hp7 hK2 hN ha1 ha hi' hj')
  rw [outerLocalWeight_of_ne_zero ha0', outerLocalWeight_of_ne_zero ha0', outerWeight_of_lt hi',
    outerWeight_of_lt hj']
  push_cast
  refine le_min (add_nonpos (min_le_left _ _) (min_le_left _ _)) ?_
  have hx := min_le_right (0 : ℚ) ((i : ℚ) + 3 * outerDelta (innerDegree n) a -
    ((ellA p (poleBound n) a : ℚ) + 4) / 2)
  have hy := min_le_right (0 : ℚ) ((j : ℚ) + 3 * outerDelta (innerDegree n) a -
    ((ellA p (poleBound n) a : ℚ) + 4) / 2)
  linarith

end Zeta5Irr
