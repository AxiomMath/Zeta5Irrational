/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.WeightsIn
public import Zeta5Irr.LocalEstimates.InTLower
public import Zeta5Irr.PrimeSum.NormExtrasExact

/-!
# The zero block of the inner weights

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²` and let `p > K / M`. Every weight `w_{0,i}` of the zero
class satisfies `|w_{0,i}| ≤ 9 M`, and consequently the zero block of the inner exponent obeys
`|2 ∑_{i < L₀} w_{0,i}| ≤ 100 M²`, where `L₀ = 4 M + 10`.

The upper bound comes from `w_{0,i} ≤ 2 i + 6 m_N - m_K + 1/2` with `i < L₀` and
`40 m_N < 3 M`. For the lower bound, `m_K < M`, `Z_c ≥ T > 2 H K / p - 21 / 20 > -2` and
`ℓ_K(c) ≤ ⌊2 K / p⌋ + 1 ≤ 2 M`.

## Main results

* `Zeta5Irr.abs_innerWeight_zero_le`: `|w_{0,i}| ≤ 9 M` for `i < L₀`.
* `Zeta5Irr.abs_two_mul_sum_innerWeight_zero_le`: `|2 ∑_{i < L₀} w_{0,i}| ≤ 100 M²`.

## Implementation notes

The source works under the standing hypotheses that `p` is a prime with `K / M < p ≤ K / 3`.
Neither primality nor `p ≤ K / 3` is used: the crude bound `T > -2`, which needs only
`K / p > 0`, replaces `T > 5`, and the resulting lower bound `w_{0,i} ≥ -M - 3` is still far
above `-9 M`. Both hypotheses are therefore dropped.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3: the inner asymptotics.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `M ≥ 40`, `K = 40 n ≥ 200 M²`, `K / M < p` and `i < L₀`, the weight of the zero class
satisfies `|w_{0,i}| ≤ 9 M`. -/
theorem abs_innerWeight_zero_le {n p M i : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hp : (poleBound n : ℚ) / M < p) (hi : i < zeroClassDim M) :
    |innerWeight n p M 0 i| ≤ 9 * M := by
  obtain ⟨hpM, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le (by omega) hK hp
  have hq : 40 * (3 * n / p) < 3 * M := forty_mul_mA_innerDegree_lt hpM
  have hpM : 40 * n < p * M := hpM
  have hK' : 200 * M ^ 2 ≤ 40 * n := hK
  have hp0 : 0 < p := by omega
  have hmK : 40 * n / p < M := (Nat.div_lt_iff_lt_mul hp0).2 (by linarith)
  have h2K : 2 * (40 * n) / p < 2 * M := (Nat.div_lt_iff_lt_mul hp0).2 (by linarith)
  have hT : (-1 : ℤ) ≤ commonClassDim n p M := by
    have h := commonClassDim_gt hM hK hp
    have : (0 : ℚ) ≤ 2 * heightRatio * poleBound n / p := by
      simp only [heightRatio]
      positivity
    have : (-2 : ℤ) < commonClassDim n p M := by
      exact_mod_cast (by linarith : (-2 : ℚ) < commonClassDim n p M)
    omega
  have hi' : (i : ℚ) + 1 ≤ 4 * M + 10 := by exact_mod_cast (show i + 1 ≤ 4 * M + 10 from hi)
  have hq' : 40 * ((3 * n / p : ℕ) : ℚ) < 3 * M := by exact_mod_cast hq
  have hmK' : ((40 * n / p : ℕ) : ℚ) + 1 ≤ M := by exact_mod_cast hmK
  have hM' : (40 : ℚ) ≤ M := by exact_mod_cast hM
  refine abs_le.2 ⟨?_, ?_⟩
  · refine le_innerWeight_zero ?_ fun c hc => ?_
    · simp only [mA, innerDegree, poleBound]
      have : (0 : ℚ) ≤ i := by positivity
      have : (0 : ℚ) ≤ ((3 * n / p : ℕ) : ℚ) := by positivity
      linarith
    · have hc' := mem_Icc.1 hc
      have hZ : (-1 : ℚ) ≤ classDim n p M c := by
        exact_mod_cast hT.trans (commonClassDim_le_classDim n p M c)
      have hl : ellA p (poleBound n) c ≤ 2 * M := by
        rcases ellA_eq_or_eq_add_one (K := poleBound n) hc'.1 hc'.2 with h | h <;>
          rw [h] <;> simp only [poleBound] <;> omega
      have hl' : (ellA p (poleBound n) c : ℚ) ≤ 2 * M := by exact_mod_cast hl
      linarith
  · refine (innerWeight_zero_le_left n p M i).trans ?_
    simp only [mA, innerDegree, poleBound]
    have : (0 : ℚ) ≤ ((40 * n / p : ℕ) : ℚ) := by positivity
    linarith

/-- **The zero block.** For `M ≥ 40`, `K = 40 n ≥ 200 M²` and `K / M < p`, the zero block of
the inner exponent satisfies `|2 ∑_{i < L₀} w_{0,i}| ≤ 100 M²`. -/
@[zeta5irr "lem_norm_zeroblock"]
theorem abs_two_mul_sum_innerWeight_zero_le {n p M : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : (poleBound n : ℚ) / M < p) :
    |2 * ∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i| ≤ 100 * M ^ 2 := by
  have hsum : |∑ i ∈ range (zeroClassDim M), innerWeight n p M 0 i| ≤
      (4 * M + 10) * (9 * M) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_card_nsmul _ _ (9 * (M : ℚ)) fun i hi =>
      abs_innerWeight_zero_le hM hK hp (mem_range.1 hi)).trans ?_
    simp
  have hM' : (40 : ℚ) ≤ M := by exact_mod_cast hM
  rw [abs_mul, abs_two]
  nlinarith

end Zeta5Irr
