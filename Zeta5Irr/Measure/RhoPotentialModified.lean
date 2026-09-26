/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoPotential

/-!
# The modified potential inequality on the half-line

For every integer `K ≥ 2` and every `t ≥ 0`,
`2 U^ρ(t) - V(t) + √t / K ≤ M₀ + √2 / K`,
where `U^ρ` is the logarithmic potential of the comparison measure `ρ`, `V` is the external
field and `M₀ = -1329/200`.

On `[0, 2]` this is the potential inequality `2 U^ρ(t) - V(t) ≤ M₀` plus `√t ≤ √2`. On
`[2, ∞)` the decay estimate bounds the left-hand side by
`G(t) = (13/10) log t + 6 α³ / t - 2π √t + √t / K`, and `G(t) ≤ G(2)`.

## Main results

* `Zeta5Irr.two_mul_logPotential_rho_sub_externalField_add_sqrt_div_le`: for `K ≥ 2` and
  `t ≥ 0`, `2 U^ρ(t) - V(t) + √t / K ≤ M₀ + √2 / K`.

## Implementation notes

The source shows that `G` decreases on `[2, ∞)` by the sign of `G'`. We argue without
derivatives: `6 α³ / t ≤ 6 α³ / 2`, and with `s = √t / √2 ≥ 1` the inequality
`log s ≤ s - 1` gives `(13/10) (log t - log 2) ≤ (13 √2 / 10) (√t - √2)`, while
`(√t - √2) / K ≤ (√t - √2) / 2`; since `13 √2 / 10 + 1/2 ≤ 2π`, this gives
`G(t) ≤ G(2)`. The bound `G(2) - √2 / K ≤ M₀` is the potential inequality's decay bound at
`t = 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.7 (The potential inequality on the half-line).
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- **The modified potential inequality**: for every integer `K ≥ 2` and every `t ≥ 0`,
`2 U^ρ(t) - V(t) + √t / K ≤ M₀ + √2 / K`, where `M₀ = -1329/200`. -/
@[zeta5irr "lem_rho_potential_modified"]
theorem two_mul_logPotential_rho_sub_externalField_add_sqrt_div_le {K : ℕ} (hK : 2 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    2 * logPotential (rho.map ((↑) : ℝ → ℂ)) t - externalField t + √t / K ≤
      (potentialBound : ℝ) + √2 / K := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  rcases le_total t 2 with ht2 | ht2
  · have h1 := two_mul_logPotential_rho_sub_externalField_le_potentialBound ht
    have h2 : √t / K ≤ √2 / K := by gcongr
    linarith
  · have hD := two_mul_logPotential_rho_sub_externalField_le ht2
    have hG2 := decayBound_le_potentialBound (le_refl (2 : ℝ))
    have ht0 : 0 < t := by linarith
    have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
    rw [hα] at hD hG2
    have h2 : (0 : ℝ) < √2 := by positivity
    have hs2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
    have h32 : √2 < 3 / 2 := by
      rw [sqrt_lt' (by norm_num)]
      norm_num
    have hst : √2 ≤ √t := sqrt_le_sqrt ht2
    have hlog : log t - log 2 ≤ √2 * (√t - √2) := by
      have := log_le_sub_one_of_pos (div_pos (sqrt_pos.2 ht0) h2)
      rw [log_div (sqrt_pos.2 ht0).ne' h2.ne', log_sqrt ht0.le, log_sqrt (by norm_num)] at this
      have hdiv : 2 * (√t / √2 - 1) = √2 * (√t - √2) := by
        field_simp
        nlinarith [hs2]
      linarith
    have hinv : 6 * (3 / 40 : ℝ) ^ 3 / t ≤ 6 * (3 / 40) ^ 3 / 2 := by gcongr
    have hKdiv : (√t - √2) / K ≤ (√t - √2) / 2 := by gcongr
    have hkey : 13 / 10 * (√2 * (√t - √2)) + (√t - √2) / 2 ≤ 2 * π * (√t - √2) := by
      have : 13 / 10 * √2 + 1 / 2 ≤ 2 * π := by linarith [pi_gt_three]
      nlinarith
    nlinarith [show √t / K - √2 / K = (√t - √2) / K by ring]

end Zeta5Irr
