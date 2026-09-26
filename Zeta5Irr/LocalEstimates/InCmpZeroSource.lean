/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La
public import Zeta5Irr.LocalEstimates.WeightsIn
public import Zeta5Irr.LocalEstimates.InTUpper

/-!
# The ordinary inner weights lie below the top of the zero-class source

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, and let `p` be a prime with `K / M < p ≤ K / 3`. For
`1 ≤ a ≤ m°` and `0 ≤ i < L_a`, the weight of the inner range satisfies
`w_{a,i} ≤ 2 L₀ + 6 m_N - m_K + 1/2`.

Indeed `i + b_a < L_a + b_a = Z_a ≤ T + 1`, so `w_{a,i} = i + b_a - (ℓ_K(a) + 4) / 2 ≤ T - 2`.
From `T < 2 H K / p` and `K / p < M` we get `T < 23 M / 10`. On the other side `L₀ = 4 M + 10`,
`m_N ≥ 0` and `m_K ≤ K / p < M`, so `2 L₀ + 6 m_N - m_K + 1/2 ≥ 7 M + 41 / 2`, which exceeds
`23 M / 10 - 2`.

## Main results

* `Zeta5Irr.innerWeight_le_zeroClassDim_of_odd`: the bound for any odd `p > 1` with `K < p M`.
* `Zeta5Irr.innerWeight_le_zeroClassDim`: the bound under the hypotheses of the source.

## Implementation notes

* The source assumes `p ≤ K / 3` and `a ≤ m°`; neither is used. Of the remaining hypotheses
  only `1 ≤ a`, `i < L_a`, `K / M < p` and the oddness of `p` enter; for a prime `p` oddness
  follows from `p > K / M ≥ 200 M`.
* The integer `K` is `poleBound n = 40 n` and `N` is `innerDegree n = 3 n`, so the statement
  is in terms of `n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6: the inner range, the weights.
-/

@[expose] public section

namespace Zeta5Irr

/-- For an odd `p > 1` with `K < p M` (where `K = 40 n`), `1 ≤ a` and `0 ≤ i < L_a`,
`w_{a,i} ≤ 2 L₀ + 6 m_N - m_K + 1/2`. -/
theorem innerWeight_le_zeroClassDim_of_odd {n p M a i : ℕ} (hodd : Odd p) (hp1 : 1 < p)
    (hpK : poleBound n < p * M) (ha : 1 ≤ a) (hi : (i : ℤ) < innerClassDim n p M a) :
    innerWeight n p M a i ≤
      2 * (zeroClassDim M : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2 := by
  rw [innerWeight_of_ne_zero n p M (by omega)]
  have hT := commonClassDim_mul_lt_of_odd hodd hp1 hpK
  have hLa := innerClassDim_def n p M a
  have hε := extraIndicator_le_one n p M a
  -- `m_K < M`
  have hmK : mA p (poleBound n) < M := by
    have h1 : mA p (poleBound n) * p ≤ poleBound n := Nat.div_mul_le_self _ _
    by_contra h
    have : M * p ≤ mA p (poleBound n) * p := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  -- `40 T < 92 M`
  have hTM : 40 * commonClassDim n p M < 92 * M := by
    have hp0 : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
    have hpK' : (poleBound n : ℤ) < p * M := by exact_mod_cast hpK
    simp only [poleBound] at hpK'
    push_cast at hpK'
    refine lt_of_mul_lt_mul_right (a := (p : ℤ)) ?_ hp0.le
    nlinarith
  -- the key integer inequality `2 (i + b_a) - ℓ_K(a) ≤ 4 L₀ + 12 m_N - 2 m_K - 3`
  have key : 2 * ((i : ℤ) + innerClassOrder p (innerDegree n) a) -
      (ellA p (poleBound n) a : ℤ) ≤
      4 * (zeroClassDim M : ℤ) + 12 * mA p (innerDegree n) - 2 * mA p (poleBound n) + 5 := by
    have : (0 : ℤ) ≤ ellA p (poleBound n) a := by positivity
    have : (0 : ℤ) ≤ mA p (innerDegree n) := by positivity
    have : (mA p (poleBound n) : ℤ) < M := by exact_mod_cast hmK
    simp only [cast_zeroClassDim]
    omega
  have key' : ((2 * ((i : ℤ) + innerClassOrder p (innerDegree n) a) -
      (ellA p (poleBound n) a : ℤ) : ℤ) : ℚ) ≤
      ((4 * (zeroClassDim M : ℤ) + 12 * mA p (innerDegree n) - 2 * mA p (poleBound n) + 5 :
        ℤ) : ℚ) := by
    exact_mod_cast key
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_natCast]
    at key'
  linarith

/-- **The ordinary inner weights against the zero-class source.** Let `M ≥ 40`, let
`K = 40 n ≥ 200 M²`, and let `p` be a prime with `K / M < p`. For `1 ≤ a` and `0 ≤ i < L_a`,
`2 L₀ + 6 m_N - m_K + 1/2 ≥ w_{a,i}`. The source also assumes `p ≤ K / 3` and `a ≤ m°`,
which are not needed. -/
@[zeta5irr "lem_in_cmp_zero_source"]
theorem innerWeight_le_zeroClassDim {n p M a i : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : p.Prime) (hpK : (poleBound n : ℝ) / M < p)
    (ha : 1 ≤ a) (hi : (i : ℤ) < innerClassDim n p M a) :
    innerWeight n p M a i ≤
      2 * (zeroClassDim M : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2 := by
  obtain ⟨hlt, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le (by omega) hK hpK
  have hp3 : 2 < p := by omega
  exact innerWeight_le_zeroClassDim_of_odd (hp.odd_of_ne_two hp3.ne') hp.one_lt hlt ha hi

end Zeta5Irr
