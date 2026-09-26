/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotArcsineMono
public import Zeta5Irr.Measure.RhoSupport

/-!
# The potential of `ρ` is nonincreasing to the left of `b₁`

For `s ≤ t ≤ b₁` the logarithmic potential of the rational arcsine measure
`ρ = ∑ⱼ cⱼ ω_{[aⱼ,bⱼ]}` satisfies `U^ρ(t) ≤ U^ρ(s)`. Since every weight `cⱼ` is nonnegative, it
suffices to prove the inequality for each arcsine measure `ω_{[aⱼ,bⱼ]}`, and since the intervals
are nested, `t ≤ b₁ ≤ bⱼ`. For a single arcsine measure `ω_{[a,b]}` and `s ≤ t ≤ b` the potential
is constant `log ((b - a)/4)` on `[a, b]` and increases with the distance to the midpoint to the
left of `a`, which gives `U^{ω_{[a,b]}}(t) ≤ U^{ω_{[a,b]}}(s)` in each of the three cases
`t ≤ a`, `a ≤ s` and `s < a < t`.

## Main results

* `Zeta5Irr.logPotential_arcsineMeasure_le_of_le`: for `a < b` and `s ≤ t ≤ b`,
  `U^{ω_{[a,b]}}(t) ≤ U^{ω_{[a,b]}}(s)`.
* `Zeta5Irr.logPotential_rho_eq_sum`: `U^ρ(t) = ∑ⱼ cⱼ U^{ω_{[aⱼ, bⱼ]}}(t)`.
* `Zeta5Irr.logPotential_rho_le_of_le`: for `s ≤ t ≤ b₁`, `U^ρ(t) ≤ U^ρ(s)`.

## Implementation notes

* The source assumes `0 ≤ s`; the argument does not use it, and the result is stated for all
  real `s ≤ t ≤ b₁`.
* The potential of `ρ` is the Bochner integral of `u ↦ log |t - u|`; splitting it into the sixteen
  potentials of the arcsine measures uses that this function is integrable against each
  `ω_{[aⱼ,bⱼ]}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- **Monotonicity of the arcsine potential to the left of `b`.** For reals `a < b` and
`s ≤ t ≤ b`, `U^{ω_{[a,b]}}(t) ≤ U^{ω_{[a,b]}}(s)`. -/
theorem logPotential_arcsineMeasure_le_of_le {a b s t : ℝ} (hab : a < b) (hst : s ≤ t)
    (htb : t ≤ b) :
    logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t ≤
      logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) s := by
  -- the case `t ≤ a`, where both points lie to the left of the interval
  have key : ∀ {s t : ℝ}, s ≤ t → t ≤ a →
      logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t ≤
        logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) s := fun {s t} hst hta ↦ by
    refine logPotential_arcsineMeasure_mono hab (Or.inl hta) (Or.inl (hst.trans hta)) ?_
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  rcases le_total t a with hta | hat
  · exact key hst hta
  rcases le_total a s with has | hsa
  · rw [logPotential_arcsineMeasure hab ⟨hat, htb⟩,
      logPotential_arcsineMeasure hab ⟨has, hst.trans htb⟩]
  · rw [logPotential_arcsineMeasure hab ⟨hat, htb⟩,
      ← logPotential_arcsineMeasure hab (left_mem_Icc.2 hab.le)]
    exact key hsa le_rfl

/-- The potential of `ρ` is the combination `U^ρ(t) = ∑ⱼ cⱼ U^{ω_{[aⱼ, bⱼ]}}(t)` of the
potentials of its sixteen arcsine measures. -/
theorem logPotential_rho_eq_sum (t : ℝ) :
    logPotential (rho.map ((↑) : ℝ → ℂ)) t = ∑ j : Fin 16,
      (rhoC j : ℝ) * logPotential ((arcsineMeasure (rhoA j) (rhoB j)).map ((↑) : ℝ → ℂ)) t := by
  simp_rw [logPotential_map_ofReal]
  rw [rho, integral_finsetSum_measure fun j _ ↦
    (integrable_log_abs_sub_arcsineMeasure (rhoA_lt_rhoB_real j) t).smul_measure
      ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (by exact_mod_cast rhoC_nonneg j)]

/-- **The potential of `ρ` is nonincreasing to the left of `b₁`**: for `s ≤ t ≤ b₁`,
`U^ρ(t) ≤ U^ρ(s)`. -/
@[zeta5irr "lem_rho_pot_mono_left"]
theorem logPotential_rho_le_of_le {s t : ℝ} (hst : s ≤ t) (ht : t ≤ rhoB 0) :
    logPotential (rho.map ((↑) : ℝ → ℂ)) t ≤ logPotential (rho.map ((↑) : ℝ → ℂ)) s := by
  rw [logPotential_rho_eq_sum, logPotential_rho_eq_sum]
  refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast rhoC_nonneg j)
  have hb : (rhoB 0 : ℝ) ≤ rhoB j := by exact_mod_cast strictMono_rhoB.monotone (Fin.zero_le j)
  exact logPotential_arcsineMeasure_le_of_le (rhoA_lt_rhoB_real j) hst (ht.trans hb)

end Zeta5Irr
