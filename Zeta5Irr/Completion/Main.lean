/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Completion.FinalInt
public import Zeta5Irr.Completion.FinalDegree
public import Zeta5Irr.Completion.FinalDecay
public import Zeta5Irr.Completion.ClearDenominators

/-!
# `ζ(5)` is irrational

Let `ξ = ζ(5)`. Suppose `ξ = a / b` with `a ∈ ℤ` and `b ≥ 1`. For every `n ≥ 200000` the
polynomial `Q_n` has integer coefficients and degree `37 n`, so `b ^ (37 n) Q_n(a / b)` is an
integer; it is positive because `Q_n(ξ) > 0`. On the other hand `Q_n(ξ) < exp(-(139/5) n²)`
for all large `n`, so `b ^ (37 n) Q_n(ξ) < exp(37 n log b - (139/5) n²) < 1` once `n` is large
enough. A positive integer smaller than `1` does not exist, so `ξ` is irrational.

## Main results

* `Zeta5Irr.irrational_zetaFive`: `ζ(5)` is irrational.

## Implementation notes

A rational number is written as `q.num / q.den` with `q : ℚ`, so the denominator is positive
from the start and no change of sign of the pair `(a, b)` is needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- **`ζ(5)` is irrational.** The real number `ξ = ζ(5)` is not rational. -/
@[zeta5irr "thm_main"]
theorem irrational_zetaFive : Irrational zetaFive := by
  rintro ⟨q, hq⟩
  set b : ℕ := q.den
  have hb : (0 : ℝ) < b := by exact_mod_cast q.den_pos
  obtain ⟨n₀, hn₀, hdecay⟩ := eval_Qn_zetaFive_lt_exp
  obtain ⟨m, hm⟩ := exists_nat_gt (185 * Real.log b / 139)
  set n : ℕ := max n₀ m + 1
  have hn : 200000 ≤ n := by omega
  have hnm : 185 * Real.log b / 139 < n := hm.trans (by exact_mod_cast (by omega : m < n))
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- Step 1: `b ^ (37 n) Q_n(ξ)` is an integer.
  obtain ⟨P, hP⟩ := Qn_mem_lifts hn
  rw [coe_mapRingHom] at hP
  have hdeg : P.natDegree ≤ 37 * n := by
    rw [← natDegree_Qn n, ← hP, natDegree_map_eq_of_injective Int.cast_injective]
  obtain ⟨z, hz⟩ := exists_int_eq_pow_mul_eval_div (K := ℝ) hdeg q.num
    (b := (b : ℤ)) (by exact_mod_cast q.den_nz)
  have hξ : ((q.num : ℤ) : ℝ) / ((b : ℤ) : ℝ) = zetaFive := by
    rw [← hq, Rat.cast_def]; push_cast; rfl
  rw [hξ, hP] at hz
  -- Step 2: it is positive.
  have hpos : (0 : ℝ) < z := hz ▸ mul_pos (pow_pos (by exact_mod_cast hb) _)
    (eval_Qn_zetaFive_pos n)
  -- Step 3: it is smaller than `1`.
  have hlt : (z : ℝ) < 1 := by
    rw [← hz]
    push_cast
    calc (b : ℝ) ^ (37 * n) * (Qn n).eval zetaFive
        < (b : ℝ) ^ (37 * n) * Real.exp (-(139 / 5) * (n : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left (hdecay n (by omega)) (pow_pos hb _)
      _ = Real.exp (n * (37 * Real.log b - 139 / 5 * n)) := by
          rw [← Real.exp_log hb, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_log hb]
          push_cast; ring_nf
      _ < 1 := by
          rw [Real.exp_lt_one_iff]
          refine mul_neg_of_pos_of_neg hn_pos ?_
          rw [div_lt_iff₀ (by norm_num)] at hnm
          linarith
  -- Step 4: a positive integer smaller than `1` does not exist.
  have h1 : (1 : ℝ) ≤ z := Int.cast_one_le_of_pos (by exact_mod_cast hpos)
  linarith

end Zeta5Irr
