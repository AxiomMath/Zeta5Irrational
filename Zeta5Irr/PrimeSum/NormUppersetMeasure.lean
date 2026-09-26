/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormUpperset

/-!
# The Lebesgue measure of the step set `S(x)`

For `x : ℝ` the step set `S(x)` of `Zeta5Irr.normUpperSet` has Lebesgue measure `{2x}/2`,
where `{y} = y - ⌊y⌋` is the fractional part. Indeed, if `{x} < 1/2` then `⌊2x⌋ = 2⌊x⌋`, so
`{2x} = 2{x}`, and `S(x) = (0, {x}]` has measure `{x}`; if `{x} ≥ 1/2` then
`⌊2x⌋ = 2⌊x⌋ + 1`, so `{2x} = 2{x} - 1`, and `S(x) = [1 - {x}, 1/2)` has measure `{x} - 1/2`.

## Main results

* `Zeta5Irr.fract_two_mul`: `{2x}` is `2{x}` or `2{x} - 1` according as `{x} < 1/2` or not.
* `Zeta5Irr.volume_normUpperSet_eq`: `vol S(x) = {2x}/2`.
* `Zeta5Irr.volume_real_normUpperSet`: the same, as a real number.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2 (The step structure of the pole counts).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- The fractional part of `2x`: it is `2{x}` if `{x} < 1/2`, and `2{x} - 1` otherwise. -/
theorem fract_two_mul (x : ℝ) :
    Int.fract (2 * x) =
      if Int.fract x < 1 / 2 then 2 * Int.fract x else 2 * Int.fract x - 1 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have hx : 2 * x = 2 * Int.fract x + ((2 * ⌊x⌋ : ℤ) : ℝ) := by
    push_cast; rw [Int.fract]; ring
  rw [Int.fract_eq_iff]
  split_ifs with h
  · refine ⟨by linarith, by linarith, 2 * ⌊x⌋, by rw [hx]; ring⟩
  · refine ⟨by linarith, by linarith, 2 * ⌊x⌋ + 1, by rw [hx]; push_cast; ring⟩

/-- The Lebesgue measure of the step set `S(x)` is `{2x}/2`. -/
@[zeta5irr "lem_norm_upperset_measure"]
theorem volume_normUpperSet_eq (x : ℝ) :
    volume (normUpperSet x) = ENNReal.ofReal (Int.fract (2 * x) / 2) := by
  rw [volume_normUpperSet, fract_two_mul]
  congr 1
  split_ifs <;> ring

/-- The Lebesgue measure of the step set `S(x)`, as a real number, is `{2x}/2`. -/
theorem volume_real_normUpperSet (x : ℝ) :
    volume.real (normUpperSet x) = Int.fract (2 * x) / 2 := by
  rw [measureReal_def, volume_normUpperSet_eq,
    ENNReal.toReal_ofReal (div_nonneg (Int.fract_nonneg _) zero_le_two)]

end Zeta5Irr
