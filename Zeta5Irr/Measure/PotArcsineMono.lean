/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.ArcsinePotential
public import Zeta5Irr.Measure.PotArcsineOff

/-!
# Monotonicity of the arcsine potential off its interval

For reals `a < b`, write `m = (a + b)/2` and `r = (b - a)/2`. At points `t` with `t ≤ a` or
`b ≤ t` the logarithmic potential of the arcsine measure `ω_{[a,b]}` depends only on the
distance `s = |t - m| ≥ r`, through `Ψ(s) = log ((s + √(s² - r²)) / 2)`, and `Ψ` is monotone.
Hence `U^{ω_{[a,b]}}(t₁) ≤ U^{ω_{[a,b]}}(t₂)` whenever `|t₁ - m| ≤ |t₂ - m|`.

## Main results

* `Zeta5Irr.logPotential_arcsineMeasure_of_notMem_Ioo`: the formula
  `U^{ω_{[a,b]}}(t) = log ((|t - m| + √((t - a)(t - b))) / 2)` for `t ∉ (a, b)`, including the
  endpoints.
* `Zeta5Irr.logPotential_arcsineMeasure_mono`: the potential is monotone in `|t - m|` on the
  complement of `(a, b)`.

## Implementation notes

Since `(t - a)(t - b) = (t - m)² - r²`, the function `Ψ` is written directly in terms of `t`;
monotonicity then follows from that of `√` and `log`, without introducing `Ψ` separately.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.2 (The arcsine measure and its potential).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

/-- For reals `a < b` and `t` with `t ≤ a` or `b ≤ t`,
`U^{ω_{[a,b]}}(t) = log ((|t - (a + b)/2| + √((t - a)(t - b))) / 2)`. At the endpoints this is
`log ((b - a)/4)`. -/
theorem logPotential_arcsineMeasure_of_notMem_Ioo {a b t : ℝ} (hab : a < b)
    (ht : t ≤ a ∨ b ≤ t) :
    logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t =
      Real.log ((|t - (a + b) / 2| + √((t - a) * (t - b))) / 2) := by
  rcases ht with ht | ht
  · rcases ht.lt_or_eq with ht | rfl
    · exact logPotential_arcsineMeasure_of_notMem hab (Or.inl ht)
    · rw [logPotential_arcsineMeasure hab (left_mem_Icc.2 hab.le), sub_self, zero_mul,
        Real.sqrt_zero, add_zero, abs_of_neg (by linarith)]
      congr 1
      ring
  · rcases ht.lt_or_eq with ht | rfl
    · exact logPotential_arcsineMeasure_of_notMem hab (Or.inr ht)
    · rw [logPotential_arcsineMeasure hab (right_mem_Icc.2 hab.le), sub_self, mul_zero,
        Real.sqrt_zero, add_zero, abs_of_pos (by linarith)]
      congr 1
      ring

/-- **Monotonicity of the arcsine potential.** For reals `a < b` and `t₁, t₂` each lying outside
the open interval `(a, b)` with `|t₁ - (a + b)/2| ≤ |t₂ - (a + b)/2|`,
`U^{ω_{[a,b]}}(t₁) ≤ U^{ω_{[a,b]}}(t₂)`. -/
@[zeta5irr "lem_pot_arcsine_mono"]
theorem logPotential_arcsineMeasure_mono {a b t₁ t₂ : ℝ} (hab : a < b)
    (ht₁ : t₁ ≤ a ∨ b ≤ t₁) (ht₂ : t₂ ≤ a ∨ b ≤ t₂)
    (h : |t₁ - (a + b) / 2| ≤ |t₂ - (a + b) / 2|) :
    logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t₁ ≤
      logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t₂ := by
  rw [logPotential_arcsineMeasure_of_notMem_Ioo hab ht₁,
    logPotential_arcsineMeasure_of_notMem_Ioo hab ht₂]
  have hs : ∀ t : ℝ, (t - a) * (t - b) = |t - (a + b) / 2| ^ 2 - ((b - a) / 2) ^ 2 := by
    intro t; rw [sq_abs]; ring
  have hr : (b - a) / 2 ≤ |t₁ - (a + b) / 2| := by
    rcases ht₁ with ht | ht
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  refine Real.log_le_log (by linarith [Real.sqrt_nonneg ((t₁ - a) * (t₁ - b))]) ?_
  refine div_le_div_of_nonneg_right (add_le_add h (Real.sqrt_le_sqrt ?_)) zero_le_two
  rw [hs, hs]
  have : |t₁ - (a + b) / 2| ^ 2 ≤ |t₂ - (a + b) / 2| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

end Zeta5Irr
