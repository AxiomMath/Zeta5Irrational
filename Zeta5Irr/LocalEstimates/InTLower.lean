/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InT
public import Mathlib.Data.Int.Star

/-!
# A lower bound for the common class dimension `T`

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²` and let `p` be a prime with `K / M < p ≤ K / 3`. The
common class dimension `T = ⌊(h - L₀ + 3 (N - m_N)) / m°⌋` then satisfies
`T > 2 H K / p - 21 / 20`. Indeed `h + 3 N = H K`, so the floor bound gives
`T > 2 (H K - L₀ - 3 m_N) / (p - 1) - 1 ≥ 2 H K / p - (2 L₀ + 6 m_N) / (p - 1) - 1`, and the
error term `(2 L₀ + 6 m_N) / (p - 1)` is below `1 / 20` because `p > 200 M` and
`m_N < 3 M / 40`.

## Main results

* `Zeta5Irr.commonClassDim_gt`: `T > 2 H K / p - 21 / 20`.

## Implementation notes

* The source assumes that `p` is prime and that `p ≤ K / 3`. Neither hypothesis is used: the
  bound `m° ≤ (p - 1) / 2` holds for every `p`, and `p > K / M ≥ 200 M` already forces `m° > 0`.
  Both hypotheses are therefore dropped.
* The inequality is stated in `ℚ`, where the height ratio `H = 23 / 20` lives. The proof clears
  denominators and argues in `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- For `M ≥ 40`, `K = 40 n ≥ 200 M²` and `K / M < p`, the common class dimension satisfies
`T > 2 H K / p - 21 / 20`. -/
@[zeta5irr "lem_in_T_lower"]
theorem commonClassDim_gt {n p M : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hp : (poleBound n : ℚ) / M < p) :
    2 * heightRatio * poleBound n / p - 21 / 20 < commonClassDim n p M := by
  obtain ⟨hpM, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le (by omega) hK hp
  -- `m_N = ⌊N / p⌋` satisfies `40 m_N < 3 M`.
  have hq : 40 * (3 * n / p) < 3 * M := forty_mul_mA_innerDegree_lt hpM
  simp only [poleBound] at hK hpM
  have hm : 2 * mStar p + 1 ≤ p := by rw [mStar_def]; omega
  have hm0 : 0 < mStar p := by rw [mStar_def]; omega
  have hT := lt_mStar_mul_commonClassDim_add (n := n) (M := M) hm0
  simp only [matrixOrder, innerDegree, mA, cast_zeroClassDim] at hT
  set T := commonClassDim n p M
  set m := mStar p
  set q := 3 * n / p
  have hn : 200 * M ≤ n := by nlinarith
  -- The numerator is nonnegative, hence so is `T + 1`.
  have hT1 : 0 ≤ T + 1 := by
    by_contra! h
    have : (m : ℤ) * (T + 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    push_cast at hT
    have hq' : (40 * q : ℤ) < 3 * M := by exact_mod_cast hq
    nlinarith
  have hprod : 0 ≤ ((p : ℤ) - 1 - 2 * m) * (T + 1) :=
    mul_nonneg (by omega) hT1
  have key : 1840 * (n : ℤ) < 20 * p * T + 21 * p := by
    push_cast at hT
    have hq' : (40 * q : ℤ) < 3 * M := by exact_mod_cast hq
    have h200' : (200 * M : ℤ) < p := by exact_mod_cast h200
    have hM' : (40 : ℤ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp0]
  have key' : 1840 * (n : ℚ) < 20 * p * T + 21 * p := by exact_mod_cast key
  simp only [heightRatio, poleBound]
  push_cast
  linarith

end Zeta5Irr
