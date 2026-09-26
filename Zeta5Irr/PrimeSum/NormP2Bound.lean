/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormP2
public import Zeta5Irr.PrimeSum.NormG0Max

/-!
# A uniform bound on the second periodic antiderivative

The second periodic antiderivative `𝒫₂(x) = (74 / α) G₀({α x}) - λ G₀({x})` is bounded
uniformly: `|𝒫₂(x)| ≤ 16` for every `x ∈ ℝ`. Both fractional parts lie in `[0, 1]`, where
`|G₀| ≤ 1 / (36 √3)`, so the triangle inequality gives
`|𝒫₂(x)| ≤ (74 / α + λ) / (36 √3) = 118511 / (4320 √3)`, and
`118511² = 14044857121 < 14332723200 = 3 · 69120²` shows this is less than `16`.

## Main results

* `Zeta5Irr.abs_secondPeriodicAntideriv_le`: `|𝒫₂(x)| ≤ 16` for all `x ∈ ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open Set Real

/-- **The second periodic antiderivative is bounded**: `|𝒫₂(x)| ≤ 16` for every `x ∈ ℝ`. -/
@[zeta5irr "lem_norm_P2_bound"]
theorem abs_secondPeriodicAntideriv_le (x : ℝ) : |secondPeriodicAntideriv x| ≤ 16 := by
  have hfr (y : ℝ) : Int.fract y ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have h1 := abs_cubicKernel_le (hfr ((innerRatio : ℝ) * x))
  have h2 := abs_cubicKernel_le (hfr x)
  have hc : (1 : ℝ) / (36 * √3) ≤ 16 * 120 / 118511 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (√3 - 118511 / 69120), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg 3]
  unfold secondPeriodicAntideriv
  simp only [innerRatio, orderRatio] at h1 ⊢
  push_cast at h1 ⊢
  calc |74 / (3 / 40 : ℝ) * cubicKernel (Int.fract (3 / 40 * x)) -
        37 / 40 * cubicKernel (Int.fract x)|
      ≤ |74 / (3 / 40 : ℝ) * cubicKernel (Int.fract (3 / 40 * x))| +
        |37 / 40 * cubicKernel (Int.fract x)| := abs_sub _ _
    _ = 2960 / 3 * |cubicKernel (Int.fract (3 / 40 * x))| +
        37 / 40 * |cubicKernel (Int.fract x)| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2960 / 3 * (16 * 120 / 118511) + 37 / 40 * (16 * 120 / 118511) := by
      gcongr <;> linarith
    _ = 16 := by norm_num

end Zeta5Irr
