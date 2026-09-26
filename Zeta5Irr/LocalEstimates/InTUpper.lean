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
# An upper bound for the common class dimension `T`

Let `M ≥ 40`, let `K = 40 n` with `K ≥ 200 M²`, and let `p` be a prime with
`K / M < p ≤ K / 3`. Then the common class dimension satisfies `T < 2 H K / p`, where
`H = 23 / 20` is the height ratio.

Since `h + 3 N = H K`, the definition of `T` as a floor gives
`m° T ≤ H K - L₀ - 3 m_N ≤ H K - L₀` with `m° = (p - 1) / 2`, so it suffices that
`p L₀ > H K`. This follows from `p > K / M`, because `H M = 23 M / 20 < 4 M + 10 = L₀`.

## Main results

* `Zeta5Irr.commonClassDim_lt_of_odd`: `T < 2 H K / p` for any odd `p > 1` with `K / M < p`.
* `Zeta5Irr.commonClassDim_lt`: `T < 2 H K / p` under the hypotheses of the source.

## Implementation notes

* The source assumes `p ≤ K / 3`; this upper bound on `p` is not needed and is omitted. Of the
  remaining hypotheses only `0 < M`, `K / M < p` and the oddness of `p` are used; for a prime
  `p` oddness follows from `p > K / M ≥ 200 M ≥ 8000`.
* The integer `K` is `poleBound n = 40 n`, so the statement is in terms of `n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The integer form of the bound: if `p > 1` is odd and `K < p M`, then `T p < 2 H K = 92 n`. -/
theorem commonClassDim_mul_lt_of_odd {n M p : ℕ} (hodd : Odd p) (hp1 : 1 < p)
    (hpK : poleBound n < p * M) : commonClassDim n p M * p < 92 * n := by
  have h2 := two_mul_mStar_add_one hodd
  have hm : 0 < mStar p := by omega
  have hle := mStar_mul_commonClassDim_le (n := n) (M := M) hm
  have hmA : (0 : ℤ) ≤ mA p (innerDegree n) := by positivity
  simp only [matrixOrder, innerDegree, zeroClassDim, poleBound] at hle hmA hpK
  push_cast at hle hmA
  have hpK' : (40 * n : ℤ) < p * M := by exact_mod_cast hpK
  have hp2 : (2 * mStar p + 1 : ℤ) = p := by exact_mod_cast h2
  have hm' : (0 : ℤ) < mStar p := by exact_mod_cast hm
  rw [← hp2]
  -- `2 m T ≤ 92 n - 2 L₀` and `(2 m + 1) L₀ > 46 n`
  nlinarith [mul_pos hm' hm']

/-- **Upper bound for `T`**, general form: if `p > 1` is odd, `0 < M` and `K / M < p`, then
`T < 2 H K / p`. -/
theorem commonClassDim_lt_of_odd {n M p : ℕ} (hodd : Odd p) (hp1 : 1 < p) (hM : 0 < M)
    (hpK : (poleBound n : ℝ) / M < p) :
    (commonClassDim n p M : ℝ) < 2 * heightRatio * poleBound n / p := by
  have hpK' : poleBound n < p * M := lt_mul_of_div_lt hM hpK
  have key := commonClassDim_mul_lt_of_odd hodd hp1 hpK'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [lt_div_iff₀ hp0, heightRatio, poleBound]
  have : ((commonClassDim n p M * p : ℤ) : ℝ) < ((92 * n : ℤ) : ℝ) := by exact_mod_cast key
  push_cast at this ⊢
  linarith

/-- **Upper bound for `T`.** Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, and let `p` be a prime with
`K / M < p`. Then `T < 2 H K / p`. The source also assumes `p ≤ K / 3`, which is not needed. -/
@[zeta5irr "lem_in_T_upper"]
theorem commonClassDim_lt {n M p : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hp : p.Prime) (hpK : (poleBound n : ℝ) / M < p) :
    (commonClassDim n p M : ℝ) < 2 * heightRatio * poleBound n / p := by
  have hM0 : 0 < M := by omega
  obtain ⟨-, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le hM0 hK hpK
  have hp3 : 2 < p := by omega
  exact commonClassDim_lt_of_odd (hp.odd_of_ne_two hp3.ne') hp.one_lt hM0 hpK

end Zeta5Irr
