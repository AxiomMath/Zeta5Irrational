/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.ScalingFactor
public import Zeta5Irr.Measure.Cstar
public import Zeta5Irr.RealDeterminant.LogFactorialUpper
public import Zeta5Irr.RealDeterminant.RealSumLog2i

/-!
# An upper bound for `log S_K`

With `K = 40 n`, `N = 3 n`, `h = 37 n`, `α = 3/40` and `λ = 37/40`, the scaling factor `S_K`
satisfies, for every `n ≥ 1`,
`log S_K ≤ (2λ - 12αλ - 2λ²) K² log K + C_* K² + 6h log K + 6h`,
where `C_*` is the norm constant.

Taking logarithms of the positive rational `S_K` gives
`log S_K = 2h log (K!) + (h - 1) log 4 - 12h log (N!) - 2 ∑_{i=1}^{h-1} log ((2i)!)`.
Each term is bounded by a Stirling-type estimate; after writing `log N = log K + log α` and
`log (2h) = log K + log (2λ)`, the terms of order `K² log K`, `K²` and `K log K` combine to the
first three terms of the bound, and the remaining terms of order `h` add up to
`(-10 + 4 log (37/20) + log 4) h ≤ 6h`.

## Main results

* `Zeta5Irr.log_scalingFactor_eq`: the expansion of `log S_K` as a sum of logarithms.
* `Zeta5Irr.log_scalingFactor_le`: the upper bound for `log S_K`.

## Implementation notes

The source bounds the leftover logarithms numerically (`log (37/20) < 0.616`, `log 4 < 1.39`).
Since the bracket only needs to be at most `6`, the cruder `log x ≤ x - 1` suffices, and is
used instead.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (the Gram integral and scaling).
-/

@[expose] public section

namespace Zeta5Irr

open Nat Finset

/-- The logarithm of the scaling factor:
`log S_K = 2h log (K!) + (h - 1) log 4 - 12h log (N!) - 2 ∑_{i=1}^{h-1} log ((2i)!)`. -/
theorem log_scalingFactor_eq (n : ℕ) :
    Real.log (scalingFactor n : ℝ) =
      2 * (matrixOrder n : ℝ) * Real.log ((poleBound n)! : ℝ) +
        ((matrixOrder n - 1 : ℕ) : ℝ) * Real.log 4 -
        12 * (matrixOrder n : ℝ) * Real.log ((innerDegree n)! : ℝ) -
        2 * ∑ i ∈ Ico 1 (matrixOrder n), Real.log ((2 * i)! : ℝ) := by
  have hI : Icc 1 (matrixOrder n - 1) = Ico 1 (matrixOrder n) := by
    ext i; simp only [mem_Icc, mem_Ico]; omega
  have hprod : 0 < ∏ i ∈ Ico 1 (matrixOrder n), (((2 * i)! : ℕ) : ℝ) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  rw [scalingFactor, hI]
  push_cast
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hprod.ne', Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_prod (fun i _ => by positivity)]
  simp only [Real.log_pow, ← Finset.mul_sum]
  push_cast
  ring

/-- **Upper bound for `log S_K`.** For every `n ≥ 1`,
`log S_K ≤ (2λ - 12αλ - 2λ²) K² log K + C_* K² + 6h log K + 6h`. -/
@[zeta5irr "lem_real_SK"]
theorem log_scalingFactor_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (scalingFactor n : ℝ) ≤
      (2 * (orderRatio : ℝ) - 12 * (innerRatio : ℝ) * orderRatio - 2 * (orderRatio : ℝ) ^ 2) *
          (poleBound n : ℝ) ^ 2 * Real.log (poleBound n) +
        normConstant * (poleBound n : ℝ) ^ 2 +
        6 * (matrixOrder n : ℝ) * Real.log (poleBound n) + 6 * matrixOrder n := by
  rw [log_scalingFactor_eq]
  have hK := log_factorial_le (poleBound n)
  have hN := mul_log_sub_add_one_le_log_factorial (m := innerDegree n)
    (by simp [innerDegree]; omega)
  have hH := neg_two_mul_sum_log_factorial_two_mul_le (h := matrixOrder n)
    (by simp [matrixOrder]; omega)
  have h1 : (((matrixOrder n - 1 : ℕ)) : ℝ) = matrixOrder n - 1 := by
    rw [Nat.cast_sub (by simp [matrixOrder]; omega)]; simp
  rw [h1]
  simp only [poleBound, innerDegree, matrixOrder, normConstant, orderRatio, innerRatio] at *
  push_cast at *
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.log (40 * (n : ℝ)) with hL
  have hNL : Real.log (3 * (n : ℝ)) = Real.log (3 / 40) + L := by
    rw [hL, ← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hHL : Real.log (2 * (37 * (n : ℝ))) = Real.log (37 / 20) + L := by
    rw [hL, ← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hLpos : 0 ≤ L := Real.log_nonneg (by linarith)
  have hb : Real.log (37 / 20) ≤ 37 / 20 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (2 * (37 / 40 : ℝ)) = Real.log (37 / 20) := by norm_num
  rw [hNL] at hN
  rw [hHL] at hH
  rw [h2]
  nlinarith

end Zeta5Irr
