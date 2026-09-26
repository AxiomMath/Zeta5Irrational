/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoPotMonoLeft

/-!
# The potential of `ρ` is monotone to the right of `a₁`

For `a₁ ≤ s ≤ t` the logarithmic potential of the rational arcsine measure
`ρ = ∑ⱼ cⱼ ω_{[aⱼ, bⱼ]}` satisfies `U^ρ(s) ≤ U^ρ(t)`.

The potential of `ρ` is the combination `∑ⱼ cⱼ U^{ω_{[aⱼ, bⱼ]}}` with nonnegative weights, so it
suffices to treat a single arcsine measure `ω_{[a,b]}` with `a ≤ a₁`. Its potential is constant,
equal to `log ((b - a)/4)`, on `[a, b]`, and is monotone in `|t - (a + b)/2|` to the right of `b`;
hence it is monotone on `[a, ∞)`.

## Main results

* `Zeta5Irr.monotoneOn_logPotential_arcsineMeasure`: the potential of `ω_{[a,b]}` is monotone
  on `[a, ∞)`.
* `Zeta5Irr.logPotential_rho_mono_right`: for `a₁ ≤ s ≤ t`, `U^ρ(s) ≤ U^ρ(t)`.

## Implementation notes

* The splitting `U^ρ = ∑ⱼ cⱼ U^{ω_{[aⱼ, bⱼ]}}` is `Zeta5Irr.logPotential_rho_eq_sum`.
* The rows are indexed by `Fin 16` from `0`, so `a₁` of the source is `rhoA 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Real

/-- For reals `a < b`, the logarithmic potential of the arcsine measure `ω_{[a,b]}` is monotone
on `[a, ∞)`: it is constant on `[a, b]` and increases with `|t - (a + b)/2|` beyond `b`. -/
theorem monotoneOn_logPotential_arcsineMeasure {a b : ℝ} (hab : a < b) :
    MonotoneOn (fun t : ℝ ↦ logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t)
      (Ici a) := by
  -- beyond `b` the potential increases with the distance to the midpoint
  have hfar : ∀ {s t : ℝ}, b ≤ s → s ≤ t →
      logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) s ≤
        logPotential ((arcsineMeasure a b).map ((↑) : ℝ → ℂ)) t := fun hs hst ↦
    logPotential_arcsineMeasure_mono hab (Or.inr hs) (Or.inr (hs.trans hst)) (by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith)
  intro s hs t ht hst
  simp only [mem_Ici] at hs ht
  dsimp only
  rcases le_or_gt b s with hbs | hsb
  · exact hfar hbs hst
  rw [logPotential_arcsineMeasure hab ⟨hs, hsb.le⟩]
  rcases le_or_gt t b with htb | hbt
  · rw [logPotential_arcsineMeasure hab ⟨ht, htb⟩]
  · rw [← logPotential_arcsineMeasure hab (right_mem_Icc.2 hab.le)]
    exact hfar le_rfl hbt.le

/-- **The potential of `ρ` is monotone to the right of `a₁`**: for `a₁ ≤ s ≤ t`,
`U^ρ(s) ≤ U^ρ(t)`. -/
@[zeta5irr "lem_rho_pot_mono_right"]
theorem logPotential_rho_mono_right {s t : ℝ} (hs : (rhoA 0 : ℝ) ≤ s) (hst : s ≤ t) :
    logPotential (rho.map ((↑) : ℝ → ℂ)) s ≤ logPotential (rho.map ((↑) : ℝ → ℂ)) t := by
  rw [logPotential_rho_eq_sum, logPotential_rho_eq_sum]
  refine Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast rhoC_nonneg j)
  have hj : (rhoA j : ℝ) ≤ s :=
    le_trans (by exact_mod_cast strictAnti_rhoA.antitone (Fin.zero_le j)) hs
  exact monotoneOn_logPotential_arcsineMeasure (rhoA_lt_rhoB_real j) hj
    (hj.trans hst) hst

end Zeta5Irr
