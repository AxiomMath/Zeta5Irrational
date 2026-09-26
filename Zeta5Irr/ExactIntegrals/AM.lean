/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.ExactIntegrals.Astar
public import Mathlib.Tactic.ENatToNat

/-!
# The margin `A_M` at mesh `M`

For an integer `M ≥ 1` the margin at mesh `M` is the real number
`A_M = A_* + 7 λ / M - (2923/240 - 1/4) / M² + 32 / M³`,
where `A_*` is the final rational margin and `λ = 37/40` is the order ratio.
It is a rational perturbation of `A_*` of size `O(1/M)`, and tends to `A_*` as `M → ∞`.

## Main definitions

* `Zeta5Irr.AM`: the margin `A_M`.

## Main results

* `Zeta5Irr.AM_eq_cast`: `A_M` is the image in `ℝ` of an explicit rational number.
* `Zeta5Irr.tendsto_AM_atTop`: `A_M → A_*` as `M → ∞`.

## Implementation notes

`A_M` is defined for every `M : ℕ`, with `M` cast to `ℝ` and real division; at `M = 0` the
three correction terms vanish by the convention `x / 0 = 0`, so `A_0 = A_*`. The source's
hypothesis `M ≥ 1` is carried by the statements that need it. The constants `A_*` and `λ`
are rational and are coerced to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.5 (the final rational margin).
-/

@[expose] public section

namespace Zeta5Irr

/-- The margin at mesh `M`:
`A_M = A_* + 7 λ / M - (2923/240 - 1/4) / M² + 32 / M³`. -/
@[zeta5irr "def_AM"]
noncomputable def AM (M : ℕ) : ℝ :=
  (Astar : ℝ) + 7 * (orderRatio : ℝ) / M - (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 + 32 / (M : ℝ) ^ 3

/-- `A_M` is the coercion of the rational number
`A_* + 7 λ / M - (2923/240 - 1/4) / M² + 32 / M³`. -/
theorem AM_eq_cast (M : ℕ) :
    AM M = ((Astar + 7 * orderRatio / M - (2923 / 240 - 1 / 4) / (M : ℚ) ^ 2 +
      32 / (M : ℚ) ^ 3 : ℚ) : ℝ) := by
  simp [AM]

/-- At `M = 0` the correction terms vanish by the convention `x / 0 = 0`. -/
@[simp]
theorem AM_zero : AM 0 = Astar := by
  simp [AM]

/-- `A_M → A_*` as `M → ∞`. -/
theorem tendsto_AM_atTop : Filter.Tendsto AM Filter.atTop (nhds (Astar : ℝ)) := by
  have h1 : Filter.Tendsto (fun M : ℕ => ((M : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds (x := (Astar : ℝ))).add
    (h1.const_mul (7 * (orderRatio : ℝ)))).sub
    ((h1.pow 2).const_mul (2923 / 240 - 1 / 4 : ℝ)) |>.add ((h1.pow 3).const_mul (32 : ℝ))
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    sub_zero] at h
  refine h.congr fun M => ?_
  simp only [AM, div_eq_mul_inv, inv_pow]

end Zeta5Irr
