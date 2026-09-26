/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.Potential
public import Zeta5Irr.Measure.Rho
public import Zeta5Irr.Measure.V
public import Zeta5Irr.Measure.VStar

/-!
# The interval bound `𝓑(l, r)`

To verify the potential inequality `2 U^ρ - V ≤ M₀` on `[0, 2]`, the interval is cut into
finitely many cells `[l, r]`, and on each cell the function `2 U^ρ - V` is majorised by the
interval bound
`𝓑(l, r) = 2 max (U^ρ(l), U^ρ(r)) - W(l, r)`, where the subtracted term `W(l, r)` is
`V(r)` if `r ≤ q₋`, `V(l)` if `l ≥ q₊`, and the floor `V_*` otherwise. Here `U^ρ` is the
logarithmic potential of the comparison measure `ρ`, `V` is the external field, and
`q₋ < q₊` bracket the minimum of `V`: the field decreases on `[0, q₋]` and increases on
`[q₊, ∞)`, and `V_*` is a lower bound for `V` on `[q₋, q₊]`.

## Main definitions

* `Zeta5Irr.potBound`: the interval bound `𝓑(l, r)`.

## Main results

* `Zeta5Irr.potBound_of_le_minLower`: `𝓑(l, r) = 2 max (U^ρ(l), U^ρ(r)) - V(r)` when
  `r ≤ q₋`.
* `Zeta5Irr.potBound_of_minUpper_le`: `𝓑(l, r) = 2 max (U^ρ(l), U^ρ(r)) - V(l)` when
  `l ≤ r` and `q₊ ≤ l`.
* `Zeta5Irr.potBound_of_mem`: `𝓑(l, r) = 2 max (U^ρ(l), U^ρ(r)) - V_*` when `q₋ < r` and
  `l < q₊`.

## Implementation notes

* The measure `ρ` lives on `ℝ`, while the potential is defined for measures on `ℂ`; `U^ρ(t)`
  is the potential of the pushforward of `ρ` along `ℝ → ℂ`, evaluated at the real point `t`.
* The hypothesis `l ≤ r` of the source is not part of the definition, which is a total
  function of two real variables; lemmas about `𝓑` assume it where they need it. The three
  cases are tested in the source's order, so for `l ≤ r` they are exclusive: `r ≤ q₋` and
  `q₊ ≤ l` cannot hold together since `q₋ < q₊`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6: the interval bound and the partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- The interval bound
`𝓑(l, r) = 2 max (U^ρ(l), U^ρ(r)) - (V(r) if r ≤ q₋, V(l) if q₊ ≤ l, V_* otherwise)`,
where `U^ρ` is the logarithmic potential of the comparison measure `ρ` (pushed forward to
`ℂ`), `V` is the external field, `V_*` its floor, and `q₋ < q₊` the bracket of the minimum
of `V`. It is meant for `l ≤ r`. -/
@[zeta5irr "def_pot_bound"]
noncomputable def potBound (l r : ℝ) : ℝ :=
  2 * max (logPotential (rho.map ((↑) : ℝ → ℂ)) l)
      (logPotential (rho.map ((↑) : ℝ → ℂ)) r) -
    if r ≤ (externalFieldMinLower : ℝ) then externalField r
    else if (externalFieldMinUpper : ℝ) ≤ l then externalField l
    else externalFieldFloor

/-- On a cell to the left of the bracket, `r ≤ q₋`, the interval bound subtracts `V(r)`. -/
theorem potBound_of_le_minLower {l r : ℝ} (hr : r ≤ (externalFieldMinLower : ℝ)) :
    potBound l r =
      2 * max (logPotential (rho.map ((↑) : ℝ → ℂ)) l)
        (logPotential (rho.map ((↑) : ℝ → ℂ)) r) - externalField r := by
  simp only [potBound, hr, ↓reduceIte]

/-- On a cell to the right of the bracket, `q₊ ≤ l ≤ r`, the interval bound subtracts
`V(l)`. -/
theorem potBound_of_minUpper_le {l r : ℝ} (hlr : l ≤ r)
    (hl : (externalFieldMinUpper : ℝ) ≤ l) :
    potBound l r =
      2 * max (logPotential (rho.map ((↑) : ℝ → ℂ)) l)
        (logPotential (rho.map ((↑) : ℝ → ℂ)) r) - externalField l := by
  have hq : (externalFieldMinLower : ℝ) < externalFieldMinUpper := by
    exact_mod_cast externalFieldMinLower_lt_upper
  simp only [potBound, show ¬r ≤ (externalFieldMinLower : ℝ) by linarith, hl, ↓reduceIte]

/-- On a cell meeting the bracket, `q₋ < r` and `l < q₊`, the interval bound subtracts the
floor `V_*`. -/
theorem potBound_of_mem {l r : ℝ} (hr : (externalFieldMinLower : ℝ) < r)
    (hl : l < (externalFieldMinUpper : ℝ)) :
    potBound l r =
      2 * max (logPotential (rho.map ((↑) : ℝ → ℂ)) l)
        (logPotential (rho.map ((↑) : ℝ → ℂ)) r) - externalFieldFloor := by
  simp only [potBound, hr.not_ge, hl.not_ge, ↓reduceIte]

end Zeta5Irr
