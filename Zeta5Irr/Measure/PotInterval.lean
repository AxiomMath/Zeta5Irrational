/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.PotGridNotation
public import Zeta5Irr.Measure.PotTable

/-!
# The dyadic intervals `J_{j,d,k}`

For a triple `(j, d, k)` of the refinement table `𝒯`, the interval `J_{j,d,k}` is the `k`-th of
the `2^d` intervals of equal length into which the grid interval `[Aⱼ, Aⱼ₊₁]` is cut:
`J_{j,d,k} = [Aⱼ + (Aⱼ₊₁ - Aⱼ) k / 2^d, Aⱼ + (Aⱼ₊₁ - Aⱼ) (k + 1) / 2^d]`.

## Main definitions

* `Zeta5Irr.potIntervalLeft`: the left endpoint `Aⱼ + (Aⱼ₊₁ - Aⱼ) k / 2^d` of `J_{j,d,k}`.
* `Zeta5Irr.potIntervalRight`: the right endpoint `Aⱼ + (Aⱼ₊₁ - Aⱼ) (k + 1) / 2^d`.
* `Zeta5Irr.potInterval`: the closed interval `J_{j,d,k}` between them.

## Main results

* `Zeta5Irr.mem_potInterval`: membership in `J_{j,d,k}` in terms of the two endpoints.
* `Zeta5Irr.potIntervalRight_eq_potIntervalLeft_succ`: the right endpoint of `J_{j,d,k}` is the
  left endpoint of `J_{j,d,k+1}`.
* `Zeta5Irr.potIntervalRight_sub_potIntervalLeft`: `J_{j,d,k}` has length
  `(Aⱼ₊₁ - Aⱼ) / 2^d`.
* `Zeta5Irr.potIntervalLeft_zero`, `Zeta5Irr.potIntervalRight_two_pow`: `J_{j,d,0}` starts at
  `Aⱼ` and `J_{j,d,2^d-1}` ends at `Aⱼ₊₁`.
* `Zeta5Irr.lt_of_mem_potTable`: every triple `(j, d, k) ∈ 𝒯` has `j < 35`, so that
  `J_{j,d,k}` is defined for it.

## Implementation notes

* The grid `A` is indexed by `Fin 36`, so the grid index of `J_{j,d,k}` is `j : Fin 35`, and
  the two ends of the grid interval are `A j.castSucc` and `A j.succ`. The table `𝒯` is a set
  of triples of natural numbers; `Zeta5Irr.lt_of_mem_potTable` supplies the bound `j < 35`
  that turns its first coordinate into an element of `Fin 35`.
* The endpoints are defined for all `d k : ℕ`, not only for the members of `𝒯`, and are
  exposed separately from the interval since the bound on `J_{j,d,k}` is evaluated at them.
* The grid points are rational; the interval is a subset of `ℝ`, with the grid cast to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.6: the interval bound and the partition of `[0, 2]`.
-/

@[expose] public section

namespace Zeta5Irr

/-- The left endpoint `Aⱼ + (Aⱼ₊₁ - Aⱼ) k / 2^d` of the dyadic interval `J_{j,d,k}`. -/
@[zeta5irr "def_pot_interval"]
noncomputable def potIntervalLeft (j : Fin 35) (d k : ℕ) : ℝ :=
  potGrid j.castSucc + (potGrid j.succ - potGrid j.castSucc) * (k / 2 ^ d)

/-- The right endpoint `Aⱼ + (Aⱼ₊₁ - Aⱼ) (k + 1) / 2^d` of the dyadic interval `J_{j,d,k}`. -/
@[zeta5irr "def_pot_interval"]
noncomputable def potIntervalRight (j : Fin 35) (d k : ℕ) : ℝ :=
  potGrid j.castSucc + (potGrid j.succ - potGrid j.castSucc) * ((k + 1) / 2 ^ d)

/-- The dyadic interval
`J_{j,d,k} = [Aⱼ + (Aⱼ₊₁ - Aⱼ) k / 2^d, Aⱼ + (Aⱼ₊₁ - Aⱼ) (k + 1) / 2^d]`, the `k`-th of the
`2^d` intervals of equal length into which the grid interval `[Aⱼ, Aⱼ₊₁]` is cut. -/
@[zeta5irr "def_pot_interval"]
noncomputable def potInterval (j : Fin 35) (d k : ℕ) : Set ℝ :=
  Set.Icc (potIntervalLeft j d k) (potIntervalRight j d k)

/-- A point lies in `J_{j,d,k}` if and only if it lies between its two endpoints. -/
theorem mem_potInterval {j : Fin 35} {d k : ℕ} {x : ℝ} :
    x ∈ potInterval j d k ↔ potIntervalLeft j d k ≤ x ∧ x ≤ potIntervalRight j d k :=
  Set.mem_Icc

/-- The interval `J_{j,d,k}` is the closed interval between its two endpoints. -/
theorem potInterval_eq_Icc (j : Fin 35) (d k : ℕ) :
    potInterval j d k = Set.Icc (potIntervalLeft j d k) (potIntervalRight j d k) :=
  rfl

/-- The right endpoint of `J_{j,d,k}` is the left endpoint of `J_{j,d,k+1}`. -/
theorem potIntervalRight_eq_potIntervalLeft_succ (j : Fin 35) (d k : ℕ) :
    potIntervalRight j d k = potIntervalLeft j d (k + 1) := by
  simp [potIntervalRight, potIntervalLeft]

/-- The interval `J_{j,d,k}` has length `(Aⱼ₊₁ - Aⱼ) / 2^d`. -/
theorem potIntervalRight_sub_potIntervalLeft (j : Fin 35) (d k : ℕ) :
    potIntervalRight j d k - potIntervalLeft j d k =
      ((potGrid j.succ : ℝ) - potGrid j.castSucc) / 2 ^ d := by
  simp only [potIntervalRight, potIntervalLeft]
  ring

/-- The first interval `J_{j,d,0}` starts at the grid point `Aⱼ`. -/
@[simp]
theorem potIntervalLeft_zero (j : Fin 35) (d : ℕ) :
    potIntervalLeft j d 0 = potGrid j.castSucc := by
  simp [potIntervalLeft]

/-- The last interval `J_{j,d,2^d-1}` ends at the grid point `Aⱼ₊₁`. -/
theorem potIntervalRight_two_pow (j : Fin 35) (d : ℕ) :
    potIntervalRight j d (2 ^ d - 1) = potGrid j.succ := by
  have h : ((2 ^ d - 1 : ℕ) : ℝ) + 1 = 2 ^ d := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [potIntervalRight, h, div_self (by positivity)]
  ring

/-- Every row `(j, d, a, b)` of the refinement table has `j < 35`. -/
theorem lt_of_mem_potTableBlocks : ∀ B ∈ potTableBlocks, B.1 < 35 := by
  decide +kernel

set_option maxRecDepth 4000 in
/-- Every triple `(j, d, k)` of the refinement table `𝒯` has `j < 35`, so that the interval
`J_{j,d,k}` is defined for it. -/
theorem lt_of_mem_potTable {j d k : ℕ} (h : (j, d, k) ∈ potTable) : j < 35 := by
  obtain ⟨a, b, hB, -⟩ := mem_potTable.1 h
  exact lt_of_mem_potTableBlocks (j, d, a, b) hB

end Zeta5Irr
