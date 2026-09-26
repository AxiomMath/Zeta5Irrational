/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VFormula
public import Zeta5Irr.Measure.RhoPotFar

/-!
# Decay of `2 U^ρ - V` on the half-line

For `t ≥ 2`,
`2 U^ρ(t) - V(t) ≤ (13/10) log t + 6 α³ / t - 2π √t`,
where `U^ρ` is the logarithmic potential of the measure `ρ`, `V` is the external field and
`α = 3/40`. The potential is bounded above by `2 λ log t = (37/20) log t`. The field is bounded
below term by term from its closed form: `log (1 + t) ≥ log t + 2 / (1 + 2t)`,
`log (t + α²) ≤ log t + α² / t`, `arctan z ≥ z - z³/3` for `z ≥ 0` (applied at `z = 1/√t`),
and `arctan z ≤ z` for `z ≥ 0` (applied at `z = α/√t`). What remains is
`2 / (3t) - 2 / (1 + 2t) ≤ 0`, which holds as `t > 1`.

## Main results

* `Zeta5Irr.sub_pow_three_div_three_le_arctan`: `z - z³/3 ≤ arctan z` for `z ≥ 0`.
* `Zeta5Irr.two_mul_logPotential_rho_sub_externalField_le`: for `t ≥ 2`,
  `2 U^ρ(t) - V(t) ≤ (13/10) log t + 6 α³ / t - 2π √t`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.7 (The potential inequality on the half-line).
-/

@[expose] public section

namespace Zeta5Irr

open Real Set

/-- The cubic Taylor lower bound for the arctangent: `z - z³/3 ≤ arctan z` for `z ≥ 0`. -/
theorem sub_pow_three_div_three_le_arctan {z : ℝ} (hz : 0 ≤ z) : z - z ^ 3 / 3 ≤ arctan z := by
  let h : ℝ → ℝ := fun z ↦ arctan z - z + z ^ 3 / 3
  have hd : ∀ z, HasDerivAt h (1 / (1 + z ^ 2) - 1 + z ^ 2) z := fun z ↦
    (((hasDerivAt_arctan z).sub (hasDerivAt_id' z)).add
      ((hasDerivAt_pow 3 z).div_const 3)).congr_deriv (by push_cast; ring)
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun x _ ↦ (hd x).continuousAt.continuousWithinAt
    · exact fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hd x).deriv]
      rw [show 1 / (1 + x ^ 2) - 1 + x ^ 2 = x ^ 4 / (1 + x ^ 2) by field_simp; ring]
      positivity
  have := hmono (mem_Ici.2 le_rfl) hz hz
  simp [h] at this
  linarith

/-- **Decay of `2 U^ρ - V`**: for `t ≥ 2`,
`2 U^ρ(t) - V(t) ≤ (13/10) log t + 6 α³ / t - 2π √t`, where `α = 3/40` is the inner ratio. -/
@[zeta5irr "lem_V_decay"]
theorem two_mul_logPotential_rho_sub_externalField_le {t : ℝ} (ht : 2 ≤ t) :
    2 * logPotential (rho.map ((↑) : ℝ → ℂ)) t - externalField t ≤
      13 / 10 * log t + 6 * (innerRatio : ℝ) ^ 3 / t - 2 * π * √t := by
  have ht0 : 0 < t := by linarith
  have hU := logPotential_rho_le ht
  rw [externalField_eq ht0]
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hlam : (orderRatio : ℝ) = 37 / 40 := by norm_num [orderRatio]
  rw [hlam] at hU
  rw [hα]
  have h1 : log t + 2 / (1 + 2 * t) ≤ log (1 + t) := by
    have := le_log_one_add_of_nonneg (x := 1 / t) (by positivity)
    rw [show 1 + t = t * (1 + 1 / t) by field_simp; ring, log_mul ht0.ne' (by positivity)]
    have e : 2 * (1 / t) / (1 / t + 2) = 2 / (1 + 2 * t) := by field_simp
    linarith
  have h2 : log (t + (3 / 40) ^ 2) ≤ log t + (3 / 40) ^ 2 / t := by
    rw [show t + (3 / 40 : ℝ) ^ 2 = t * (1 + (3 / 40) ^ 2 / t) by field_simp,
      log_mul ht0.ne' (by positivity)]
    have := log_le_sub_one_of_pos (x := 1 + (3 / 40 : ℝ) ^ 2 / t) (by positivity)
    linarith
  have hs : 0 < √t := sqrt_pos.2 ht0
  have hst : √t * √t = t := mul_self_sqrt ht0.le
  have h3 : 2 - 2 / (3 * t) ≤ 2 * √t * arctan (1 / √t) := by
    have := sub_pow_three_div_three_le_arctan (z := 1 / √t) (by positivity)
    have e : 2 * √t * (1 / √t - (1 / √t) ^ 3 / 3) = 2 - 2 / (3 * t) := by
      rw [show (1 / √t) ^ 3 = 1 / (√t * √t * √t) by ring, hst]
      field_simp
    exact e ▸ mul_le_mul_of_nonneg_left this (by positivity)
  have h4 : 2 * √t * arctan (3 / 40 / √t) ≤ 2 * (3 / 40) := by
    have := arctan_le_self (x := 3 / 40 / √t) (by positivity)
    calc 2 * √t * arctan (3 / 40 / √t) ≤ 2 * √t * (3 / 40 / √t) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * (3 / 40) := by field_simp
  have h5 : 2 / (3 * t) ≤ 2 / (1 + 2 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have key : 2 * √t * (π + arctan (1 / √t) - 6 * arctan (3 / 40 / √t)) =
      2 * π * √t + 2 * √t * arctan (1 / √t) - 6 * (2 * √t * arctan (3 / 40 / √t)) := by ring
  have key' : 6 * (3 / 40 : ℝ) ^ 3 / t = 6 * (3 / 40) * ((3 / 40) ^ 2 / t) := by ring
  rw [key, key']
  linarith

end Zeta5Irr
