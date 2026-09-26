/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LocalEstimates.MA
public import Zeta5Irr.LocalEstimates.InL0
public import Mathlib.Tactic.ENatToNat

/-!
# The allocation density `ϖ_p(K, M)`

With `K = 40 n`, `N = 3 n` and `h = 37 n`, an integer `M` and a prime `p`, the allocation
density is the real number
`ϖ_p(K, M) = (h - L₀ + 3 (N - ⌊N / p⌋)) / (p - 1)`,
where `L₀ = 4 M + 10` is the reserved zero-class dimension and `⌊N / p⌋ = m_N`. Since
`p - 1 = 2 m°`, the integers `T` and `E` of the inner range are `T = ⌊2 ϖ_p(K, M)⌋` and
`E = (p - 1)(ϖ_p(K, M) - T / 2)`, so `ϖ_p(K, M)` carries both at once; it is the exact
analogue of `H x`, `x = K / p`, in the limiting picture.

## Main definitions

* `Zeta5Irr.allocationDensity`: the allocation density `ϖ_p(K, M)`.

## Main results

* `Zeta5Irr.allocationDensity_eq`: `ϖ_p(K, M) = (H K - L₀ - 3 m_N) / (p - 1)`, using
  `h + 3 N = H K`.
* `Zeta5Irr.sub_one_mul_allocationDensity`: `(p - 1) ϖ_p(K, M) = h - L₀ + 3 (N - m_N)` for
  `p ≠ 1`.

## Implementation notes

* The source states the definition under the standing hypotheses `M ≥ 40`, `K ∈ 40 ℤ_{>0}`
  with `K ≥ 200 M²`, and `p` prime with `K / M < p ≤ K / 3`. None of them is needed to write
  the formula down, so `ϖ_p(K, M)` is defined for all natural numbers `n`, `M`, `p`
  (with the convention `x / 0 = 0` of `ℝ` at `p = 1`), and the hypotheses are carried by
  the lemmas that use them.
* The parameter `K = 40 n` enters through `n`, as for the other parameters of the
  construction; `h`, `N`, `L₀` and `m_N` are `Zeta5Irr.matrixOrder n`,
  `Zeta5Irr.innerDegree n`, `Zeta5Irr.zeroClassDim M` and `Zeta5Irr.mA p (innerDegree n)`.
  The value is rational; it is taken in `ℝ`, where it is compared with `H K / p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3: the inner asymptotics.
-/

@[expose] public section

namespace Zeta5Irr

/-- The allocation density `ϖ_p(K, M) = (h - L₀ + 3 (N - ⌊N / p⌋)) / (p - 1)`, where
`K = 40 n`, `N = 3 n`, `h = 37 n` and `L₀ = 4 M + 10`. -/
@[zeta5irr "def_norm_alloc"]
noncomputable def allocationDensity (n M p : ℕ) : ℝ :=
  ((matrixOrder n : ℝ) - zeroClassDim M + 3 * ((innerDegree n : ℝ) - mA p (innerDegree n))) /
    ((p : ℝ) - 1)

/-- The allocation density with all parameters written out:
`ϖ_p(K, M) = (37 n - (4 M + 10) + 3 (3 n - ⌊3 n / p⌋)) / (p - 1)`. -/
theorem allocationDensity_def (n M p : ℕ) :
    allocationDensity n M p =
      (37 * (n : ℝ) - (4 * M + 10) + 3 * (3 * (n : ℝ) - ((3 * n / p : ℕ) : ℝ))) /
        ((p : ℝ) - 1) := by
  simp [allocationDensity, matrixOrder, innerDegree, mA]

/-- Since `h + 3 N = H K`, `ϖ_p(K, M) = (H K - L₀ - 3 m_N) / (p - 1)`. -/
theorem allocationDensity_eq (n M p : ℕ) :
    allocationDensity n M p =
      ((heightRatio : ℝ) * poleBound n - zeroClassDim M - 3 * mA p (innerDegree n)) /
        ((p : ℝ) - 1) := by
  rw [allocationDensity]
  congr 1
  simp only [matrixOrder, innerDegree, poleBound, heightRatio]
  push_cast
  ring

/-- For `p ≠ 1`, `(p - 1) ϖ_p(K, M) = h - L₀ + 3 (N - m_N)`. -/
theorem sub_one_mul_allocationDensity (n M : ℕ) {p : ℕ} (hp : p ≠ 1) :
    ((p : ℝ) - 1) * allocationDensity n M p =
      (matrixOrder n : ℝ) - zeroClassDim M +
        3 * ((innerDegree n : ℝ) - mA p (innerDegree n)) := by
  have : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp)
  rw [allocationDensity, mul_div_cancel₀ _ this]

end Zeta5Irr
