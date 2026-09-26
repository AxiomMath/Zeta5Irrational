/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.ArcsinePotential

/-!
# The potential of the arcsine measure off its interval

For reals `a < b` and a real `t` with `t < a` or `t > b`, the logarithmic potential of the
arcsine measure `ω_{[a,b]}` at `t` is
`U^{ω_{[a,b]}}(t) = log ((|t - (a + b)/2| + √((t - a)(t - b))) / 2)`.

Write `m = (a + b)/2`, `r = (b - a)/2 > 0` and `c = (t - m)/r`, so that `|c| > 1`, and let `μ` be
the real root of `(μ + μ⁻¹)/2 = c` with `|μ| = |c| + √(c² - 1) > 1`. Pushing the uniform measure
on the circle forward along `θ ↦ m + r cos θ` turns the potential into the circle average of
`θ ↦ log |t - m - r cos θ|`, and the Joukowski–Chebyshev identity splits this integrand as
`log (r/2) + log |e^{iθ} - μ| + log |e^{iθ} - μ⁻¹|`. The circle averages of the last two terms
are `log⁺ |μ| = log |μ|` and `log⁺ |μ⁻¹| = 0`, so the potential is `log (r |μ| / 2)`, and
`r |μ| = |t - m| + √((t - a)(t - b))`.

## Main results

* `Zeta5Irr.exists_joukowski_eq_of_one_lt_abs`: for real `c` with `|c| > 1` there is a real `μ`
  with `(μ + μ⁻¹)/2 = c` and `|μ| = |c| + √(c² - 1)`.
* `Zeta5Irr.logPotential_arcsineMeasure_of_notMem`: the formula for `U^{ω_{[a,b]}}(t)` for `t`
  outside `[a, b]`.

## Implementation notes

The arcsine measure is a measure on `ℝ`, while the logarithmic potential is defined for measures
on `ℂ`; the potential of `ω_{[a,b]}` is that of its image under the inclusion `ℝ → ℂ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.2 (The arcsine measure and its potential).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

/-- For real `c` with `1 < |c|` there is a real `μ` with `(μ + μ⁻¹)/2 = c` and
`|μ| = |c| + √(c² - 1)`. -/
lemma exists_joukowski_eq_of_one_lt_abs {c : ℝ} (hc : 1 < |c|) :
    ∃ μ : ℝ, (μ + μ⁻¹) / 2 = c ∧ |μ| = |c| + √(c ^ 2 - 1) := by
  have hc2 : 0 ≤ c ^ 2 - 1 := by
    have : 1 < c ^ 2 := by rw [← sq_abs]; nlinarith
    linarith
  set s := √(c ^ 2 - 1) with hs
  have hss : s ^ 2 = c ^ 2 - 1 := sq_sqrt hc2
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have key : ∀ d : ℝ, 1 < d → d ^ 2 = c ^ 2 → ((d + s) + (d + s)⁻¹) / 2 = d := by
    intro d hd hdc
    have hpos : 0 < d + s := by linarith
    field_simp
    nlinarith
  rcases lt_or_gt_of_ne (show c ≠ 0 by rintro rfl; simp at hc; linarith) with h | h
  · refine ⟨-(|c| + s), ?_, by rw [abs_neg, abs_of_nonneg (by positivity)]⟩
    have := key |c| hc (sq_abs c)
    rw [abs_of_neg h] at this ⊢
    rw [inv_neg]
    linarith
  · refine ⟨|c| + s, ?_, by rw [abs_of_nonneg (by positivity)]⟩
    have := key |c| hc (sq_abs c)
    rw [abs_of_pos h] at this ⊢
    exact this

/-- **Potential of the arcsine measure off its interval.** For reals `a < b` and a real `t`
with `t < a` or `b < t`,
`U^{ω_{[a,b]}}(t) = log ((|t - (a + b)/2| + √((t - a)(t - b))) / 2)`. -/
@[zeta5irr "lem_pot_arcsine_off"]
theorem logPotential_arcsineMeasure_of_notMem {a b t : ℝ} (hab : a < b) (ht : t < a ∨ b < t) :
    logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t =
      Real.log ((|t - (a + b) / 2| + √((t - a) * (t - b))) / 2) := by
  set m := (a + b) / 2 with hm
  set r := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set c := (t - m) / r with hcdef
  have hc : 1 < |c| := by
    rw [hcdef, abs_div, abs_of_pos hr0, lt_div_iff₀ hr0, one_mul]
    rcases ht with ht | ht
    · rw [abs_of_neg (by rw [hm]; linarith)]; rw [hr, hm]; linarith
    · rw [abs_of_pos (by rw [hm]; linarith)]; rw [hr, hm]; linarith
  obtain ⟨μ, hμc, hμabs⟩ := exists_joukowski_eq_of_one_lt_abs hc
  have hμ1 : 1 < |μ| := by rw [hμabs]; linarith [sqrt_nonneg (c ^ 2 - 1)]
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ1; linarith
  have hμinv : |μ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ1
  rw [logPotential_arcsineMeasure_eq_posLog hab (Complex.ofReal_ne_zero.2 hμ0)
      (by exact_mod_cast hμc), ← Complex.ofReal_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.posLog_eq_log_max_one (abs_nonneg _),
    Real.posLog_eq_log_max_one (abs_nonneg _), max_eq_right hμ1.le, max_eq_left hμinv.le,
    Real.log_one, add_zero, ← Real.log_mul hr0.ne' (by positivity),
    ← Real.log_div (by positivity) two_ne_zero]
  congr 1
  have h1 : r * |c| = |t - m| := by
    rw [hcdef, abs_div, abs_of_pos hr0, mul_div_cancel₀ _ hr0.ne']
  have h2 : r * √(c ^ 2 - 1) = √((t - a) * (t - b)) := by
    rw [← abs_of_pos hr0, ← sqrt_sq_eq_abs, ← sqrt_mul (sq_nonneg _)]
    congr 1
    rw [hcdef, mul_sub, mul_one, ← mul_pow, mul_div_cancel₀ _ hr0.ne', hm, hr]
    ring
  rw [hμabs]
  linear_combination (h1 + h2) / 2

end Zeta5Irr
