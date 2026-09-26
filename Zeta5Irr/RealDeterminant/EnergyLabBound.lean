/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.EnergyLab
public import Zeta5Irr.RealDeterminant.EnergyLogIntegral
public import Mathlib.Algebra.Order.Star.Real

/-!
# The bound `|L_{a,b}(r)| ≤ |log r|`

For `0 < a < b < ∞` and `r > 0`, the truncated zero-mass logarithmic energy
`L_{a,b}(r) = ½ ∫_a^b (e^{-s} - e^{-s r²}) / s ds` satisfies `|L_{a,b}(r)| ≤ |log r|`.
The integrand has the fixed sign of `r² - 1` on `(0, ∞)`, so truncating the integration range
to `[a, b]` can only decrease its absolute value, and the full integral over `(0, ∞)` equals
`2 log r` by Frullani's integral.

## Main results

* `Zeta5Irr.integral_exp_neg_mul_sub_exp_neg_mul_div_mem_Icc`: for `0 < α ≤ β` and
  `0 ≤ a ≤ b`, `0 ≤ ∫_a^b (e^{-αs} - e^{-βs}) / s ds ≤ log (β / α)`.
* `Zeta5Irr.abs_energyLab_le`: `|L_{a,b}(r)| ≤ |log r|`.

## Implementation notes

* The main result is stated for `0 ≤ a`, `0 ≤ b` in either order, which contains the source's
  hypothesis `0 < a < b`: the interval integral is oriented, and swapping the endpoints only
  changes the sign of `L_{a,b}(r)`.
* The source's case split `r > 1`, `r < 1`, `r = 1` becomes `1 ≤ r` versus `r ≤ 1`, each
  reduced to the two-parameter bound with `(α, β) = (1, r²)` or `(r², 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.1: zero-mass logarithmic energy.
-/

@[expose] public section

open MeasureTheory Set Real

namespace Zeta5Irr

/-- For `0 < α ≤ β` and `0 ≤ a ≤ b`, the truncated Frullani integral
`∫_a^b (e^{-αs} - e^{-βs}) / s ds` lies between `0` and the full integral `log (β / α)`. -/
theorem integral_exp_neg_mul_sub_exp_neg_mul_div_mem_Icc {α β a b : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, (exp (-α * s) - exp (-β * s)) / s ∈ Icc 0 (log (β / α)) := by
  have hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ (exp (-α * s) - exp (-β * s)) / s := fun s hs =>
    div_nonneg (sub_nonneg.2 (exp_le_exp.2 (by nlinarith [mem_Ioi.1 hs]))) (le_of_lt hs)
  have hsub : Ioc a b ⊆ Ioi 0 := fun s hs => ha.trans_lt hs.1
  rw [intervalIntegral.integral_of_le hab]
  refine ⟨setIntegral_nonneg measurableSet_Ioc fun s hs => hnn s (hsub hs), ?_⟩
  rw [← integral_exp_neg_mul_sub_exp_neg_mul_div hα (hα.trans_le hαβ)]
  refine setIntegral_mono_set
    (integrableOn_exp_neg_mul_sub_exp_neg_mul_div hα (hα.trans_le hαβ)) ?_
    hsub.eventuallyLE
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hnn s hs

/-- **Bound on the zero-mass logarithmic energy.** For `0 ≤ a`, `0 ≤ b` and `r > 0`,
`|L_{a,b}(r)| ≤ |log r|`. -/
@[zeta5irr "lem_energy_Lab_bound"]
theorem abs_energyLab_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r) :
    |energyLab a b r| ≤ |log r| := by
  wlog hab : a ≤ b generalizing a b
  · rw [energyLab_symm, abs_neg]
    exact this hb ha (le_of_not_ge hab)
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hlog : log (r ^ 2) = 2 * log r := by rw [log_pow]; push_cast; ring
  rcases le_total 1 r with h1 | h1
  · have h := integral_exp_neg_mul_sub_exp_neg_mul_div_mem_Icc one_pos
      (one_le_pow₀ h1 : (1 : ℝ) ≤ r ^ 2) ha hab
    have heq : (fun s : ℝ => (exp (-s) - exp (-s * r ^ 2)) / s) =
        fun s => (exp (-1 * s) - exp (-(r ^ 2) * s)) / s := by
      ext s; ring_nf
    rw [div_one, hlog] at h
    have hl : 0 ≤ log r := log_nonneg h1
    rw [energyLab, heq, abs_of_nonneg hl, abs_le]
    constructor <;> nlinarith [h.1, h.2]
  · have h := integral_exp_neg_mul_sub_exp_neg_mul_div_mem_Icc hr2
      (pow_le_one₀ hr.le h1 : r ^ 2 ≤ 1) ha hab
    have heq : (fun s : ℝ => (exp (-s) - exp (-s * r ^ 2)) / s) =
        fun s => -((exp (-(r ^ 2) * s) - exp (-1 * s)) / s) := by
      ext s; ring_nf
    rw [log_div one_ne_zero hr2.ne', log_one, hlog] at h
    have hl : log r ≤ 0 := log_nonpos hr.le h1
    rw [energyLab, heq, intervalIntegral.integral_neg, abs_of_nonpos hl, abs_le]
    constructor <;> nlinarith [h.1, h.2]

end Zeta5Irr
