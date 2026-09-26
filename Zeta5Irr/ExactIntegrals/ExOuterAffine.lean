/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExOuterIntegrand
public import Zeta5Irr.ExactIntegrals.ExOuterTable

/-!
# The outer integrand is affine on each row of `𝒯`

For every row `(l, r, b, c)` of the table `𝒯` and every `y` with `l < y < r`, the outer
integrand satisfies `Θ(y) = b + c y`. On such an open interval, `⌊1/y⌋` is constant, each of
the positive parts `(2 λ - j y)⁺`, `(1 + α - 3 y)⁺`, `(1 + 4 α - 3 y - ⋯)⁺`,
`(1 + α - 2 y)⁺`, `(1 + 4 α - 2 y)⁺` and each of the minima `min(α, 1 - 2 y)`,
`min(α, 1 - y)` is resolved to one of its two branches, since every threshold is an endpoint
of the table; summing the resulting affine functions gives the row's `(b, c)`.

## Main results

* `Zeta5Irr.outerIntegrand_eq_of_mem_outerTable`: `Θ(y) = b + c y` for `(l, r, b, c) ∈ 𝒯`
  and `l < y < r`.

## Implementation notes

* The source's proof tabulates the four summands of `Θ` separately and adds them row by row.
  The formal proof resolves, on each row, the floor, the rank defect (through its three
  affine pieces), and then every `if`, positive part and minimum by the sign of its argument,
  which on the open row is fixed; the resulting linear identity is closed by `ring`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.4 (The outer integral).
-/

@[expose] public section

namespace Zeta5Irr

/-- `⌊1/y⌋ = k` as soon as `k y ≤ 1 < (k + 1) y`, for `y > 0`. -/
private lemma floor_inv_eq {y : ℝ} {k : ℤ} (hy : 0 < y) (h₁ : (k : ℝ) * y ≤ 1)
    (h₂ : 1 < ((k : ℝ) + 1) * y) : ⌊y⁻¹⌋ = k := by
  rw [Int.floor_eq_iff, ← one_div, le_div_iff₀ hy, div_lt_iff₀ hy]
  exact ⟨h₁, h₂⟩

/-- For every row `(l, r, b, c)` of the outer table `𝒯` and every `y` with `l < y < r`,
the outer integrand is affine there: `Θ(y) = b + c y`. -/
@[zeta5irr "lem_ex_outer_affine"]
theorem outerIntegrand_eq_of_mem_outerTable {l r b c : ℚ} (hp : (l, r, b, c) ∈ outerTable)
    {y : ℝ} (hl : (l : ℝ) < y) (hr : y < r) : outerIntegrand y = b + c * y := by
  simp only [outerTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hlam : (orderRatio : ℝ) = 37 / 40 := by norm_num [orderRatio]
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  push_cast at hl hr ⊢ <;>
  · have hy : 0 < y := by linarith
    rw [outerIntegrand]
    first
    | rw [show ⌊y⁻¹⌋ = 2 from floor_inv_eq hy (by push_cast; linarith) (by push_cast; linarith)]
    | rw [show ⌊y⁻¹⌋ = 1 from floor_inv_eq hy (by push_cast; linarith) (by push_cast; linarith)]
    | rw [show ⌊y⁻¹⌋ = 0 from floor_inv_eq hy (by push_cast; linarith) (by push_cast; linarith)]
    first
    | rw [rankDefect_of_le (y := y) (by linarith) (by linarith)]
    | rw [rankDefect_of_ge_of_le (y := y) (by linarith) (by linarith)]
    | rw [rankDefect_of_ge (y := y) (by linarith)]
    simp only [outerLimitingFunction, hα, hlam, Finset.sum_Icc_succ_top (show 1 ≤ 5 by norm_num),
      Finset.sum_Icc_succ_top (show 1 ≤ 4 by norm_num),
      Finset.sum_Icc_succ_top (show 1 ≤ 3 by norm_num),
      Finset.sum_Icc_succ_top (show 1 ≤ 2 by norm_num), Finset.Icc_self, Finset.sum_singleton]
    push_cast
    repeat
      first
      | (rw [ite_eq_left]; on_goal 2 => linarith)
      | (rw [ite_eq_right]; on_goal 2 => (push Not; linarith))
      | (rw [posPart_eq_self.2]; on_goal 2 => linarith)
      | (rw [posPart_eq_zero.2]; on_goal 2 => linarith)
      | (rw [min_eq_left]; on_goal 2 => linarith)
      | (rw [min_eq_right]; on_goal 2 => linarith)
    ring

end Zeta5Irr
