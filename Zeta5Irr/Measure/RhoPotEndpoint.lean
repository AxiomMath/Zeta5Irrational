/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoPotMonoLeft
public import Zeta5Irr.Measure.RhoPotMonoRight

/-!
# The potential of `ρ` on an interval is bounded by its endpoint values

For `l ≤ t ≤ r` the logarithmic potential of the rational arcsine measure
`ρ = ∑ⱼ cⱼ ω_{[aⱼ, bⱼ]}` satisfies `U^ρ(t) ≤ max (U^ρ(l)) (U^ρ(r))`.

Since `a₁ < b₁`, every real `t` satisfies `t ≤ b₁` or `a₁ ≤ t`. In the first case `U^ρ` is
nonincreasing on `(-∞, b₁]`, so `U^ρ(t) ≤ U^ρ(l)`; in the second it is nondecreasing on
`[a₁, ∞)`, so `U^ρ(t) ≤ U^ρ(r)`.

## Main results

* `Zeta5Irr.logPotential_rho_le_max`: `U^ρ(t) ≤ max (U^ρ(l)) (U^ρ(r))` for `l ≤ t ≤ r`.

## Implementation notes

The source states the result for `0 ≤ l ≤ t ≤ r`. The hypothesis `0 ≤ l` is not needed,
because the monotonicity of `U^ρ` to the left of `b₁` holds on all of `(-∞, b₁]`, and it is
omitted here.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (The sixteen intervals).
-/

@[expose] public section

namespace Zeta5Irr

/-- **Endpoint bound for the potential of `ρ`**: for `l ≤ t ≤ r`,
`U^ρ(t) ≤ max (U^ρ(l)) (U^ρ(r))`. -/
@[zeta5irr "lem_rho_pot_endpoint"]
theorem logPotential_rho_le_max {l t r : ℝ} (hlt : l ≤ t) (htr : t ≤ r) :
    logPotential (rho.map ((↑) : ℝ → ℂ)) t ≤
      max (logPotential (rho.map ((↑) : ℝ → ℂ)) l)
        (logPotential (rho.map ((↑) : ℝ → ℂ)) r) := by
  have hab : (rhoA 0 : ℝ) < rhoB 0 := by exact_mod_cast rhoA_nested.2.2.1
  rcases le_total t (rhoB 0) with htb | hat
  · exact le_max_of_le_left (logPotential_rho_le_of_le hlt htb)
  · exact le_max_of_le_right (logPotential_rho_mono_right (hab.le.trans hat) htr)

end Zeta5Irr
