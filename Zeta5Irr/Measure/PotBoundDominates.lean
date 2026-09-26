/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotBound
public import Zeta5Irr.Measure.RhoPotEndpoint
public import Zeta5Irr.Measure.VStarLower

/-!
# The interval bound dominates `2 U^ρ - V`

On a cell `[l, r]` with `0 ≤ l`, the interval bound `𝓑(l, r)` majorises `2 U^ρ(t) - V(t)` for
every `t ∈ [l, r]`. The potential term is handled by the endpoint bound
`U^ρ(t) ≤ max (U^ρ(l), U^ρ(r))`; the subtracted term of `𝓑(l, r)` is at most `V(t)` in each of
its three cases: by monotonicity of `V` on `[0, q₋]` when `r ≤ q₋`, by monotonicity of `V` on
`[q₊, ∞)` when `q₊ ≤ l`, and by the floor `V_* ≤ V(t)` otherwise.

## Main results

* `Zeta5Irr.two_mul_logPotential_rho_sub_externalField_le_potBound`: for `0 ≤ l ≤ t ≤ r`,
  `2 U^ρ(t) - V(t) ≤ 𝓑(l, r)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6 (The interval bound and the partition of `[0, 2]`).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- **The interval bound dominates `2 U^ρ - V`**: for `0 ≤ l ≤ t ≤ r`,
`2 U^ρ(t) - V(t) ≤ 𝓑(l, r)`. -/
@[zeta5irr "lem_pot_bound_dominates"]
theorem two_mul_logPotential_rho_sub_externalField_le_potBound {l t r : ℝ} (hl : 0 ≤ l)
    (hlt : l ≤ t) (htr : t ≤ r) :
    2 * logPotential (rho.map ((↑) : ℝ → ℂ)) t - externalField t ≤ potBound l r := by
  have hU := logPotential_rho_le_max hlt htr
  have ht : 0 ≤ t := hl.trans hlt
  have hW : (if r ≤ (externalFieldMinLower : ℝ) then externalField r
      else if (externalFieldMinUpper : ℝ) ≤ l then externalField l
      else externalFieldFloor) ≤ externalField t := by
    split_ifs with hr hq
    · exact antitoneOn_externalField ⟨ht, htr.trans hr⟩ ⟨ht.trans htr, hr⟩ htr
    · exact monotoneOn_externalField (mem_Ici.2 hq) (mem_Ici.2 (hq.trans hlt)) hlt
    · exact externalFieldFloor_le ht
  rw [potBound]
  linarith

end Zeta5Irr
