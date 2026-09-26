/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The rational arcsine data `aⱼ, bⱼ, cⱼ`

The comparison measure `ρ = ∑ⱼ cⱼ ω_[aⱼ, bⱼ]` is a combination of sixteen arcsine measures.
For `1 ≤ j ≤ 16`, the rationals `aⱼ`, `bⱼ`, `cⱼ` are `10⁻¹²` times the integers in the `j`th
row of the following table.

| `j` | `10¹² aⱼ` | `10¹² bⱼ` | `10¹² cⱼ` |
|---:|---:|---:|---:|
| 1 | 3906748086 | 8992695531 | 10515596180 |
| 2 | 2312248264 | 15340997855 | 29471737793 |
| 3 | 1402286665 | 25730180724 | 42934365099 |
| 4 | 881725356 | 41909578246 | 58204231966 |
| 5 | 578197906 | 65851089563 | 69037621310 |
| 6 | 396324613 | 99481037884 | 78873099189 |
| 7 | 283911191 | 144325727458 | 84856120711 |
| 8 | 212206188 | 201105762729 | 88396082127 |
| 9 | 165097686 | 269345996903 | 88303382125 |
| 10 | 133347132 | 347089554156 | 85472321255 |
| 11 | 111522114 | 430806704415 | 78899184238 |
| 12 | 96349355 | 515561896511 | 70353471918 |
| 13 | 85815639 | 595448778546 | 58838976615 |
| 14 | 78667711 | 664241383483 | 44421321106 |
| 15 | 74129565 | 716160577112 | 30462865791 |
| 16 | 71741310 | 746637295669 | 5959622577 |

## Main definitions

* `Zeta5Irr.rhoANum`, `Zeta5Irr.rhoBNum`, `Zeta5Irr.rhoCNum`: the three integer columns
  `10¹² aⱼ`, `10¹² bⱼ`, `10¹² cⱼ` of the table.
* `Zeta5Irr.rhoA`, `Zeta5Irr.rhoB`, `Zeta5Irr.rhoC`: the rationals `aⱼ`, `bⱼ`, `cⱼ`.

## Main results

* `Zeta5Irr.rhoA_eq`, `Zeta5Irr.rhoB_eq`, `Zeta5Irr.rhoC_eq`: each rational is its integer
  entry divided by `10¹²`.
* `Zeta5Irr.rhoC_nonneg`: the weights `cⱼ` are nonnegative.
* `Zeta5Irr.mul_rhoA`, `Zeta5Irr.mul_rhoB`, `Zeta5Irr.mul_rhoC`: multiplying by `10¹²`
  recovers the integer entry, which reduces comparisons between the rationals to comparisons
  between the integers of the table.

## Implementation notes

* The rows are indexed by `Fin 16`, starting at `0`: row `j` of the source, for `1 ≤ j ≤ 16`,
  is the index `j - 1`. Thus `a₁` is `rhoA 0` and `a₁₆` is `rhoA 15`.
* All entries of the table are nonnegative integers, so the columns are functions
  `Fin 16 → ℕ`; the rationals are their casts to `ℚ` divided by `10¹²`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3 (Table 1): the rational arcsine measure.
-/

@[expose] public section

namespace Zeta5Irr

/-- The column `10¹² aⱼ` of the table of the rational arcsine measure; row `j` of the source
is the index `j - 1`. -/
def rhoANum : Fin 16 → ℕ :=
  ![3906748086, 2312248264, 1402286665, 881725356,
    578197906, 396324613, 283911191, 212206188,
    165097686, 133347132, 111522114, 96349355,
    85815639, 78667711, 74129565, 71741310]

/-- The column `10¹² bⱼ` of the table of the rational arcsine measure; row `j` of the source
is the index `j - 1`. -/
def rhoBNum : Fin 16 → ℕ :=
  ![8992695531, 15340997855, 25730180724, 41909578246,
    65851089563, 99481037884, 144325727458, 201105762729,
    269345996903, 347089554156, 430806704415, 515561896511,
    595448778546, 664241383483, 716160577112, 746637295669]

/-- The column `10¹² cⱼ` of the table of the rational arcsine measure; row `j` of the source
is the index `j - 1`. -/
def rhoCNum : Fin 16 → ℕ :=
  ![10515596180, 29471737793, 42934365099, 58204231966,
    69037621310, 78873099189, 84856120711, 88396082127,
    88303382125, 85472321255, 78899184238, 70353471918,
    58838976615, 44421321106, 30462865791, 5959622577]

/-- The left endpoints `aⱼ = 10⁻¹² · (10¹² aⱼ)` of the sixteen intervals of the rational
arcsine measure; `a_j` of the source is `rhoA (j - 1)`. -/
@[zeta5irr "not_rho_table"]
def rhoA (j : Fin 16) : ℚ := rhoANum j / 10 ^ 12

/-- The right endpoints `bⱼ = 10⁻¹² · (10¹² bⱼ)` of the sixteen intervals of the rational
arcsine measure; `b_j` of the source is `rhoB (j - 1)`. -/
@[zeta5irr "not_rho_table"]
def rhoB (j : Fin 16) : ℚ := rhoBNum j / 10 ^ 12

/-- The weights `cⱼ = 10⁻¹² · (10¹² cⱼ)` of the sixteen arcsine measures in the rational
arcsine measure; `c_j` of the source is `rhoC (j - 1)`. -/
@[zeta5irr "not_rho_table"]
def rhoC (j : Fin 16) : ℚ := rhoCNum j / 10 ^ 12

/-- The rational `rhoA j` is the integer entry `rhoANum j` divided by `10¹²`. -/
theorem rhoA_eq (j : Fin 16) : rhoA j = rhoANum j / 10 ^ 12 := rfl

/-- The rational `rhoB j` is the integer entry `rhoBNum j` divided by `10¹²`. -/
theorem rhoB_eq (j : Fin 16) : rhoB j = rhoBNum j / 10 ^ 12 := rfl

/-- The rational `rhoC j` is the integer entry `rhoCNum j` divided by `10¹²`. -/
theorem rhoC_eq (j : Fin 16) : rhoC j = rhoCNum j / 10 ^ 12 := rfl

/-- Multiplying `aⱼ` by `10¹²` recovers the integer entry of the table. -/
theorem mul_rhoA (j : Fin 16) : 10 ^ 12 * rhoA j = rhoANum j := by
  rw [rhoA]; field_simp

/-- Multiplying `bⱼ` by `10¹²` recovers the integer entry of the table. -/
theorem mul_rhoB (j : Fin 16) : 10 ^ 12 * rhoB j = rhoBNum j := by
  rw [rhoB]; field_simp

/-- Multiplying `cⱼ` by `10¹²` recovers the integer entry of the table. -/
theorem mul_rhoC (j : Fin 16) : 10 ^ 12 * rhoC j = rhoCNum j := by
  rw [rhoC]; field_simp

/-- The weights `cⱼ` of the table are nonnegative. -/
theorem rhoC_nonneg (j : Fin 16) : 0 ≤ rhoC j := by
  rw [rhoC]; positivity

end Zeta5Irr
