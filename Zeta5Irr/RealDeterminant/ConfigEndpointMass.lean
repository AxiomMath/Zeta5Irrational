/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigArcsineCdf

/-!
# The endpoint mass of the arcsine measure

For reals `a < b` the arcsine measure `ω_{[a,b]}` gives the interval `[a, a + y]` at most the
mass `√(y / (b - a))`: the arcsine density blows up at the endpoint `a` only like the inverse
square root of the distance to it.

By the distribution function of the arcsine measure the mass is `(2/π) arcsin z` with
`z = √(y / (b - a))`, and Jordan's inequality `(2/π) x ≤ sin x` on `[0, π/2]` applied at
`x = arcsin z` gives `(2/π) arcsin z ≤ z` for `0 ≤ z ≤ 1`; for `1 ≤ z` the left side is `1`.

## Main results

* `Zeta5Irr.two_div_pi_mul_arcsin_le`: `(2/π) arcsin z ≤ z` for `0 ≤ z`.
* `Zeta5Irr.arcsineMeasure_Icc_left_le`: `ω_{[a,b]}([a, a + y]) ≤ √(y / (b - a))`.
* `Zeta5Irr.measureReal_arcsineMeasure_Icc_left_le`: the same bound for the real-valued mass.

## Implementation notes

* The hypothesis `0 ≤ y` of the source is dropped: for `y < 0` the interval `[a, a + y]` has
  mass `0` and the truncated square root vanishes.
* The case `b - a ≤ y` is not treated separately through the total mass of `ω_{[a,b]}`: the
  inequality `(2/π) arcsin z ≤ z` holds for all `z ≥ 0` since `arcsin` is truncated at `π/2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real
open scoped ENNReal

/-- `(2/π) arcsin z ≤ z` for every `z ≥ 0`: Jordan's inequality at `arcsin z` for `z ≤ 1`, and
`arcsin z = π/2` for `1 ≤ z`. -/
lemma two_div_pi_mul_arcsin_le {z : ℝ} (hz : 0 ≤ z) : 2 / π * arcsin z ≤ z := by
  rcases le_or_gt 1 z with h1 | h1
  · rw [arcsin_of_one_le h1, div_mul_div_cancel₀ pi_ne_zero, div_self two_ne_zero]
    exact h1
  · calc 2 / π * arcsin z ≤ sin (arcsin z) :=
          mul_le_sin (arcsin_nonneg.2 hz) (arcsin_le_pi_div_two z)
      _ = z := sin_arcsin (by linarith) h1.le

/-- **The endpoint mass of the arcsine measure.** For `a < b`,
`ω_{[a,b]}([a, a + y]) ≤ √(y / (b - a))` for every real `y`. -/
@[zeta5irr "lem_config_endpoint_mass"]
theorem arcsineMeasure_Icc_left_le {a b : ℝ} (hab : a < b) (y : ℝ) :
    arcsineMeasure a b (Icc a (a + y)) ≤ ENNReal.ofReal √(y / (b - a)) := by
  rw [arcsineMeasure_Icc_left hab]
  exact ENNReal.ofReal_le_ofReal (two_div_pi_mul_arcsin_le (sqrt_nonneg _))

/-- The endpoint mass of the arcsine measure, as a real-valued mass:
`ω_{[a,b]}([a, a + y]) ≤ √(y / (b - a))` for every real `y`. -/
theorem measureReal_arcsineMeasure_Icc_left_le {a b : ℝ} (hab : a < b) (y : ℝ) :
    (arcsineMeasure a b).real (Icc a (a + y)) ≤ √(y / (b - a)) := by
  rw [measureReal_arcsineMeasure_Icc_left hab]
  exact two_div_pi_mul_arcsin_le (sqrt_nonneg _)

end Zeta5Irr
