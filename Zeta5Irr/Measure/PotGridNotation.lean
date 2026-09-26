/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoTableNotation
public import Zeta5Irr.Measure.VQpmNotation

/-!
# The grid `A₀, …, A₃₅` partitioning `[0, 2]`

The interval bound for the potential is proved on a partition of `[0, 2]` whose break points
are the endpoints of the sixteen arcsine intervals together with the bracket `q₋ < q₊` of the
minimum of the external field. The grid is
`A₀ = 0`, `Aⱼ = a₁₇₋ⱼ` for `1 ≤ j ≤ 16`, `A₁₇ = q₋`, `A₁₈ = q₊`,
`A₁₈₊ⱼ = bⱼ` for `1 ≤ j ≤ 16`, and `A₃₅ = 2`.

## Main definitions

* `Zeta5Irr.potGrid`: the grid point `Aᵢ`, for `0 ≤ i ≤ 35`.

## Main results

* `Zeta5Irr.potGrid_zero`: `A₀ = 0`.
* `Zeta5Irr.potGrid_rhoA`: `A₁₇₋ⱼ = aⱼ` for `1 ≤ j ≤ 16`.
* `Zeta5Irr.potGrid_seventeen`: `A₁₇ = q₋`.
* `Zeta5Irr.potGrid_eighteen`: `A₁₈ = q₊`.
* `Zeta5Irr.potGrid_rhoB`: `A₁₈₊ⱼ = bⱼ` for `1 ≤ j ≤ 16`.
* `Zeta5Irr.potGrid_thirtyFive`: `A₃₅ = 2`.

## Implementation notes

* The grid is indexed by `Fin 36`. The arcsine data `aⱼ`, `bⱼ` are indexed by `Fin 16`
  starting at `0` (`aⱼ` is `rhoA (j - 1)`), so for `k : Fin 16` the point `A₁₆₋ₖ` is `rhoA k`
  and the point `A₁₉₊ₖ` is `rhoB k`; these are the statements of `potGrid_rhoA` and
  `potGrid_rhoB`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6: the interval bound and the partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr

/-- The grid point `Aᵢ` of the partition of `[0, 2]`: `A₀ = 0`, `Aⱼ = a₁₇₋ⱼ` for
`1 ≤ j ≤ 16`, `A₁₇ = q₋`, `A₁₈ = q₊`, `A₁₈₊ⱼ = bⱼ` for `1 ≤ j ≤ 16`, and `A₃₅ = 2`. -/
@[zeta5irr "not_pot_grid"]
def potGrid (i : Fin 36) : ℚ :=
  if h₀ : i.val = 0 then 0
  else if h₁ : i.val ≤ 16 then rhoA ⟨16 - i.val, by omega⟩
  else if i.val = 17 then externalFieldMinLower
  else if i.val = 18 then externalFieldMinUpper
  else if h₂ : i.val ≤ 34 then rhoB ⟨i.val - 19, by omega⟩
  else 2

/-- The first grid point is `A₀ = 0`. -/
@[simp]
theorem potGrid_zero : potGrid 0 = 0 := rfl

/-- The grid point `A₁₆₋ₖ` is `rhoA k`; in the source's indexing, `A₁₇₋ⱼ = aⱼ` for
`1 ≤ j ≤ 16`. -/
theorem potGrid_rhoA (k : Fin 16) : potGrid ⟨16 - k.val, by omega⟩ = rhoA k := by
  have hk := k.isLt
  generalize hi : (⟨16 - k.val, by omega⟩ : Fin 36) = i
  have hv : i.val = 16 - k.val := by rw [← hi]
  unfold potGrid
  split_ifs <;> first | omega | (congr 1; ext; simp only; omega)

/-- The grid point `A₁₇` is the lower end `q₋` of the bracket of the minimum of the external
field. -/
@[simp]
theorem potGrid_seventeen : potGrid 17 = externalFieldMinLower := rfl

/-- The grid point `A₁₈` is the upper end `q₊` of the bracket of the minimum of the external
field. -/
@[simp]
theorem potGrid_eighteen : potGrid 18 = externalFieldMinUpper := rfl

/-- The grid point `A₁₉₊ₖ` is `rhoB k`; in the source's indexing, `A₁₈₊ⱼ = bⱼ` for
`1 ≤ j ≤ 16`. -/
theorem potGrid_rhoB (k : Fin 16) : potGrid ⟨19 + k.val, by omega⟩ = rhoB k := by
  have hk := k.isLt
  generalize hi : (⟨19 + k.val, by omega⟩ : Fin 36) = i
  have hv : i.val = 19 + k.val := by rw [← hi]
  unfold potGrid
  split_ifs <;> first | omega | (congr 1; ext; simp only; omega)

/-- The last grid point is `A₃₅ = 2`. -/
@[simp]
theorem potGrid_thirtyFive : potGrid 35 = 2 := rfl

end Zeta5Irr
