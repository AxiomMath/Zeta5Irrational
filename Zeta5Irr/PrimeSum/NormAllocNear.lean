/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormAlloc
public import Mathlib.Algebra.Order.Star.Real

/-!
# The allocation density is close to `H K / p`

Write `x = K / p`. Since `h + 3 N = H K`, the allocation density satisfies
`ϖ_p(K, M) - H x = (H x - L₀ - 3 m_N) / (p - 1)`. When `x ≤ M` the numerator is at most
`6 M` in absolute value (using `L₀ = 4 M + 10 ≤ 4 M + M / 4` for `M ≥ 40` and
`3 m_N ≤ 3 α x ≤ 9 M / 40`), and `p - 1 ≥ p / 2` for `p ≥ 2`, so
`|ϖ_p(K, M) - H K / p| ≤ 12 M / p`.

## Main results

* `Zeta5Irr.abs_allocationDensity_sub_le`: `|ϖ_p(K, M) - H K / p| ≤ 12 M / p` whenever
  `M ≥ 40`, `p ≥ 2` and `K ≤ M p`.
* `Zeta5Irr.abs_allocationDensity_sub_le_of_lt`: the same bound under the source's
  hypothesis `K / M < p`.

## Implementation notes

* The source states the bound under the standing hypotheses (4.1): `M ≥ 40`,
  `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, and `p` prime with `K / M < p ≤ K / 3`. The proof uses
  only `M ≥ 40`, `p ≥ 2` and `x = K / p ≤ M`, so the main statement assumes just these,
  with the last in the form `K ≤ M p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

/-- The allocation density is within `12 M / p` of `H K / p`:
`|ϖ_p(K, M) - H K / p| ≤ 12 M / p` for `M ≥ 40`, `p ≥ 2` and `K ≤ M p`. -/
@[zeta5irr "lem_norm_alloc_near"]
theorem abs_allocationDensity_sub_le {n M p : ℕ} (hM : 40 ≤ M) (hp : 2 ≤ p)
    (hK : poleBound n ≤ M * p) :
    |allocationDensity n M p - (heightRatio : ℝ) * poleBound n / p| ≤ 12 * M / p := by
  rw [allocationDensity_eq]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hM' : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hK' : (40 : ℝ) * n ≤ M * p := by
    have : ((poleBound n : ℕ) : ℝ) ≤ ((M * p : ℕ) : ℝ) := by exact_mod_cast hK
    simpa [poleBound] using this
  have hm : (mA p (innerDegree n) : ℝ) * p ≤ 3 * n := by
    have : mA p (innerDegree n) * p ≤ 3 * n := by
      simpa [mA, innerDegree] using Nat.div_mul_le_self (3 * n) p
    exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ mA p (innerDegree n) := Nat.cast_nonneg _
  set m : ℝ := ((mA p (innerDegree n) : ℕ) : ℝ)
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  simp only [heightRatio, poleBound, cast_zeroClassDim]
  push_cast
  have key : (23 / 20 : ℝ) * (40 * n) / p ≤ 23 / 20 * M := by
    rw [div_le_iff₀ hp0]; nlinarith
  have hmM : 3 * m ≤ 9 / 40 * M := by
    have : 3 * m * p ≤ 9 / 40 * M * p := by nlinarith
    exact le_of_mul_le_mul_right this hp0
  have hx0 : (0 : ℝ) ≤ (23 / 20 : ℝ) * (40 * n) / p := by positivity
  have heq : (23 / 20 * (40 * (n : ℝ)) - (4 * M + 10) - 3 * m) / (p - 1) -
      23 / 20 * (40 * n) / p =
      ((23 / 20 : ℝ) * (40 * n) / p - (4 * M + 10) - 3 * m) / (p - 1) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hp1, div_le_div_iff₀ hp1 hp0]
  have hA : |(23 / 20 : ℝ) * (40 * n) / p - (4 * M + 10) - 3 * m| ≤ 6 * M := by
    rw [abs_le]; constructor <;> nlinarith
  nlinarith [abs_nonneg ((23 / 20 : ℝ) * (40 * n) / p - (4 * M + 10) - 3 * m)]

/-- The allocation density is within `12 M / p` of `H K / p` under the source's hypotheses
`M ≥ 40`, `p ≥ 2` and `K / M < p`. -/
theorem abs_allocationDensity_sub_le_of_lt {n M p : ℕ} (hM : 40 ≤ M) (hp : 2 ≤ p)
    (hpK : (poleBound n : ℝ) / M < p) :
    |allocationDensity n M p - (heightRatio : ℝ) * poleBound n / p| ≤ 12 * M / p := by
  refine abs_allocationDensity_sub_le hM hp ?_
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rw [div_lt_iff₀ hM0] at hpK
  have : (poleBound n : ℝ) < ((M * p : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this.le

end Zeta5Irr
