/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Mathlib.Algebra.Order.Star.Real

/-!
# The sawtooth slope `Φ`

The inner limiting function `R` splits as `R(x) = x Φ(x) + 𝓔(x)`, where the slope
`Φ(x) = 4λ + 2λ{x} - 12λ{αx}` is a combination of two sawtooth functions, with
`α = 3/40` and `λ = 37/40` the ratios of the construction and `{·}` the fractional part.
Since both fractional parts lie in `[0, 1)`, `Φ` takes values in `(-8λ, 6λ)`, so in
particular `|Φ(x)| ≤ 18λ`, the bound used for the integrability of `R(x) / x³`.

## Main definitions

* `Zeta5Irr.sawtoothSlope`: `Φ(x) = 4λ + 2λ{x} - 12λ{αx}`.

## Main results

* `Zeta5Irr.sawtoothSlope_lt`, `Zeta5Irr.lt_sawtoothSlope`: `-8λ < Φ(x) < 6λ`.
* `Zeta5Irr.abs_sawtoothSlope_le`: `|Φ(x)| ≤ 18λ`.
* `Zeta5Irr.measurable_sawtoothSlope`: `Φ` is measurable.
* `Zeta5Irr.sawtoothSlope_add_forty_mul_intCast`: `Φ` is periodic with period `40 = 3/α`.

## Implementation notes

* `Φ` is a total function on `ℝ`; the exceptional set `ℤ ∪ α⁻¹ℤ` on which it jumps appears
  only as a hypothesis of the lemmas that need it.
* The parameters `α` and `λ` are the rational constants `Zeta5Irr.innerRatio` and
  `Zeta5Irr.orderRatio`, coerced to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.5: the splitting of the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The sawtooth slope `Φ(x) = 4λ + 2λ{x} - 12λ{αx}`, with `α = 3/40` and `λ = 37/40`. -/
@[zeta5irr "def_norm_Phi"]
noncomputable def sawtoothSlope (x : ℝ) : ℝ :=
  4 * (orderRatio : ℝ) + 2 * orderRatio * Int.fract x -
    12 * orderRatio * Int.fract ((innerRatio : ℝ) * x)

/-- `Φ` with the fractional parts written as `x - ⌊x⌋`. -/
theorem sawtoothSlope_eq_floor (x : ℝ) :
    sawtoothSlope x = 4 * (orderRatio : ℝ) + 2 * orderRatio * (x - ⌊x⌋) -
      12 * orderRatio * ((innerRatio : ℝ) * x - ⌊(innerRatio : ℝ) * x⌋) := by
  simp only [sawtoothSlope, Int.fract]

/-- `Φ(x) < 6λ`. -/
theorem sawtoothSlope_lt (x : ℝ) : sawtoothSlope x < 6 * (orderRatio : ℝ) := by
  have hl : (0 : ℝ) < orderRatio := by exact_mod_cast orderRatio_pos
  have h1 := Int.fract_lt_one x
  have h2 := Int.fract_nonneg ((innerRatio : ℝ) * x)
  unfold sawtoothSlope
  nlinarith

/-- `-8λ < Φ(x)`. -/
theorem lt_sawtoothSlope (x : ℝ) : -8 * (orderRatio : ℝ) < sawtoothSlope x := by
  have hl : (0 : ℝ) < orderRatio := by exact_mod_cast orderRatio_pos
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one ((innerRatio : ℝ) * x)
  unfold sawtoothSlope
  nlinarith

/-- `|Φ(x)| ≤ 18λ`. -/
theorem abs_sawtoothSlope_le (x : ℝ) : |sawtoothSlope x| ≤ 18 * (orderRatio : ℝ) := by
  have hl : (0 : ℝ) < orderRatio := by exact_mod_cast orderRatio_pos
  have := sawtoothSlope_lt x
  have := lt_sawtoothSlope x
  rw [abs_le]
  constructor <;> linarith

/-- `|Φ(x)| ≤ 18`. -/
theorem abs_sawtoothSlope_le_eighteen (x : ℝ) : |sawtoothSlope x| ≤ 18 := by
  have hl : (orderRatio : ℝ) < 1 := by exact_mod_cast orderRatio_lt_one
  linarith [abs_sawtoothSlope_le x]

/-- `Φ` is measurable. -/
@[fun_prop]
theorem measurable_sawtoothSlope : Measurable sawtoothSlope := by
  unfold sawtoothSlope
  have h1 : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  have h2 : Measurable fun x : ℝ => Int.fract ((innerRatio : ℝ) * x) :=
    measurable_fract.comp (measurable_const.mul measurable_id)
  fun_prop

/-- `Φ` is periodic: `Φ(x + 40 m) = Φ(x)` for every integer `m`, since `40 α = 3`. -/
theorem sawtoothSlope_add_forty_mul_intCast (x : ℝ) (m : ℤ) :
    sawtoothSlope (x + 40 * m) = sawtoothSlope x := by
  have h1 : Int.fract (x + 40 * m) = Int.fract x := by
    have : (40 * m : ℝ) = ((40 * m : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.fract_add_intCast]
  have h2 : Int.fract ((innerRatio : ℝ) * (x + 40 * m)) =
      Int.fract ((innerRatio : ℝ) * x) := by
    have : (innerRatio : ℝ) * (x + 40 * m) = (innerRatio : ℝ) * x + ((3 * m : ℤ) : ℝ) := by
      simp only [innerRatio]; push_cast; ring
    rw [this, Int.fract_add_intCast]
  simp only [sawtoothSlope, h1, h2]

end Zeta5Irr
