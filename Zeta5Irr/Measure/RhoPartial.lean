/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.RhoTableNotation

/-!
# The partial sums `Sⱼ` of the weights of the rational arcsine measure

The weights `c₁, …, c₁₆` of the rational arcsine measure `ρ = ∑ⱼ cⱼ ω_[aⱼ, bⱼ]` have
partial sums `S₀ = 0` and `Sⱼ = ∑_{i=1}^j cᵢ` for `1 ≤ j ≤ 16`.

## Main definitions

* `Zeta5Irr.rhoPartial`: the partial sum `Sⱼ`.

## Main results

* `Zeta5Irr.rhoPartial_zero`: `S₀ = 0`.
* `Zeta5Irr.rhoPartial_eq_sum_filter`, `Zeta5Irr.rhoPartial_succ_eq_sum_filter`: `S_j` and
  `S_{j+1}` for `j : Fin 16` as sums over `i < j` and `i ≤ j`.
* `Zeta5Irr.rhoPartial_eq_sum_fin`: for `j ≤ 16`, `Sⱼ = ∑_{i=1}^j cᵢ`.
* `Zeta5Irr.rhoPartial_succ`: `S_{j+1} = Sⱼ + c_{j+1}` for `j < 16`.
* `Zeta5Irr.rhoPartial_of_le`: `Sⱼ = S₁₆` for `j ≥ 16`.
* `Zeta5Irr.rhoPartial_nonneg`, `Zeta5Irr.rhoPartial_mono`: the partial sums are nonnegative
  and nondecreasing.

## Implementation notes

* `Sⱼ` is a function on all of `ℕ`, so that differences such as `Sⱼ - S_{j-1}` need no index
  coercions. It is the sum of the weights `cᵢ` with `i ≤ j`; the weight `cᵢ` of the source is
  `rhoC (i - 1)`, so this is the sum of `rhoC i` over the indices `i : Fin 16` with `i < j`.
  For `j ≥ 16` this is constantly `S₁₆`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.3: the sixteen intervals.
-/

@[expose] public section

namespace Zeta5Irr

/-- The partial sum `Sⱼ = ∑_{i=1}^j cᵢ` of the weights of the rational arcsine measure, with
`S₀ = 0`. Since `cᵢ` is `rhoC (i - 1)`, it sums `rhoC i` over `i : Fin 16` with `i < j`. -/
@[zeta5irr "def_rho_partial"]
def rhoPartial (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin 16 => (i : ℕ) < j), rhoC i

/-- `S₀ = 0`. -/
@[simp]
theorem rhoPartial_zero : rhoPartial 0 = 0 := by
  simp [rhoPartial]

/-- The partial sums as sums over `Fin 16`: `S_{j+1}` is the sum of `cᵢ` over `i ≤ j`. -/
theorem rhoPartial_succ_eq_sum_filter (j : Fin 16) :
    rhoPartial (j + 1) = ∑ i ∈ Finset.univ.filter (· ≤ j), rhoC i := by
  simp only [rhoPartial, Nat.lt_succ_iff, Fin.le_iff_val_le_val]

/-- The partial sums as sums over `Fin 16`: `S_j` is the sum of `cᵢ` over `i < j`. -/
theorem rhoPartial_eq_sum_filter (j : Fin 16) :
    rhoPartial j = ∑ i ∈ Finset.univ.filter (· < j), rhoC i := by
  simp only [rhoPartial, Fin.lt_def]

/-- For `j ≤ 16`, `Sⱼ = ∑_{i=1}^j cᵢ`, written as a sum over the first `j` rows of the table. -/
theorem rhoPartial_eq_sum_fin {j : ℕ} (hj : j ≤ 16) :
    rhoPartial j = ∑ i : Fin j, rhoC (Fin.castLE hj i) := by
  rw [rhoPartial]
  refine Finset.sum_bij' (fun i hi => ⟨i, (Finset.mem_filter.1 hi).2⟩)
    (fun i _ => Fin.castLE hj i) ?_ ?_ ?_ ?_ ?_ <;> simp

/-- `S_{j+1} = Sⱼ + c_{j+1}` for `j < 16`. -/
theorem rhoPartial_succ {j : ℕ} (hj : j < 16) :
    rhoPartial (j + 1) = rhoPartial j + rhoC ⟨j, hj⟩ := by
  rw [rhoPartial_eq_sum_fin hj, rhoPartial_eq_sum_fin hj.le, Fin.sum_univ_castSucc]
  rfl

/-- `Sⱼ = S₁₆` for `j ≥ 16`. -/
theorem rhoPartial_of_le {j : ℕ} (hj : 16 ≤ j) : rhoPartial j = rhoPartial 16 := by
  simp only [rhoPartial]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- The partial sums `Sⱼ` are nonnegative. -/
theorem rhoPartial_nonneg (j : ℕ) : 0 ≤ rhoPartial j :=
  Finset.sum_nonneg fun i _ => rhoC_nonneg i

/-- The partial sums `Sⱼ` are nondecreasing in `j`. -/
theorem rhoPartial_mono : Monotone rhoPartial := fun j k hjk =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; omega)
    fun i _ _ => rhoC_nonneg i

end Zeta5Irr
