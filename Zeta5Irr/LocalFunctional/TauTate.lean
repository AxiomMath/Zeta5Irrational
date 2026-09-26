/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.Tactic.Polynomial.Basic

/-!
# The Tate algebra `ℚ_p⟨z⟩` and its Gauss norm

The Tate algebra `𝒜 = ℚ_p⟨z⟩` is the set of power series `f = ∑_{d ≥ 0} f_d z^d ∈ ℚ_p[[z]]`
whose coefficients tend to `0` `p`-adically, `|f_d|_p → 0`. It is a `ℚ_p`-subalgebra (in
particular a `ℚ_p`-subspace) of `ℚ_p[[z]]`, and carries the coefficient supremum norm
`‖f‖ = sup_{d ≥ 0} |f_d|_p`. For a polynomial `U ∈ ℚ_p[z]` the same formula gives
`‖U‖ = p^{-v_p^G(U)}`, where `v_p^G` is the Gauss valuation.

## Main definitions

* `Zeta5Irr.tateAlgebra p`: the Tate algebra `ℚ_p⟨z⟩` as a `ℚ_p`-subalgebra of `ℚ_[p]⟦X⟧`.
* `Zeta5Irr.tateNorm f`: the coefficient supremum norm `sup_d |f_d|_p` of `f ∈ ℚ_[p]⟦X⟧`.

## Main results

* `Zeta5Irr.mem_tateAlgebra_iff`: `f ∈ ℚ_p⟨z⟩ ↔ |f_d|_p → 0`.
* `Zeta5Irr.tateNorm_eq_iSup`: `‖f‖ = ⨆ d, ‖f_d‖`.
* `Zeta5Irr.le_tateNorm`: on `ℚ_p⟨z⟩`, every `|f_d|_p ≤ ‖f‖`.
* `Zeta5Irr.tateNorm_le_of_forall_norm_coeff_le`: conversely, a uniform bound on the
  coefficients bounds the Gauss norm; `Zeta5Irr.tateNorm_map_coe_le_one`: polynomials over
  `ℤ_p` have Gauss norm at most `1`.
* `Zeta5Irr.tateNorm_eq_zero_iff`, `Zeta5Irr.tateNorm_add_le_max`,
  `Zeta5Irr.tateNorm_smul`: the Gauss norm is a non-archimedean `ℚ_p`-vector space norm on
  `ℚ_p⟨z⟩`.
* `Zeta5Irr.tateNorm_coe_polynomial`: for `U ∈ ℚ_p[z]` with `v_p^G(U) = n`, `‖U‖ = p^{-n}`;
  together with `Zeta5Irr.tateNorm_zero` (the case `v_p^G(0) = +∞`) this is `‖U‖ = p^{-v_p^G(U)}`.

## Implementation notes

* No new type is introduced: `ℚ_p⟨z⟩` is Mathlib's ring of restricted power series
  `PowerSeries.IsRestricted.subring 1`, viewed as a `ℚ_p`-subalgebra, and the norm is Mathlib's
  `PowerSeries.gaussNorm` with radius `1`. Elements of `ℚ_p⟨z⟩` are power series together with
  a membership hypothesis, so they can be combined freely with polynomials via
  `Polynomial.toPowerSeries`.
* `tateNorm` is defined on all of `ℚ_[p]⟦X⟧`; outside `ℚ_p⟨z⟩` the supremum may be unbounded,
  in which case its value is the junk value of `iSup`. All results about it that need
  boundedness assume membership in `ℚ_p⟨z⟩`.
* Since `v_p^G` takes values in `ℤ ∪ {+∞}`, the identity `‖U‖ = p^{-v_p^G(U)}` is stated
  for a finite value `n` of `v_p^G(U)`; the value `+∞` occurs only for `U = 0`
  (`Zeta5Irr.vpG_eq_top_iff`), where `‖0‖ = 0 = p^{-∞}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4: completion at a prime.
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology

variable (p : ℕ) [Fact p.Prime]

/-- The Tate algebra `ℚ_p⟨z⟩`: power series over `ℚ_p` whose coefficients tend to `0`, as a
`ℚ_p`-subalgebra of `ℚ_[p]⟦X⟧`. -/
@[zeta5irr "def_tau_tate"]
noncomputable def tateAlgebra : Subalgebra ℚ_[p] ℚ_[p]⟦X⟧ :=
  { (PowerSeries.IsRestricted.subring 1 : Subring ℚ_[p]⟦X⟧) with
    algebraMap_mem' := fun a => PowerSeries.isRestricted_C 1 a }

variable {p}

/-- The coefficient supremum norm `‖f‖ = sup_d |f_d|_p` of a power series over `ℚ_p`, i.e. the
Gauss norm of radius `1`. -/
@[zeta5irr "def_tau_tate"]
noncomputable abbrev tateNorm (f : ℚ_[p]⟦X⟧) : ℝ :=
  PowerSeries.gaussNorm (‖·‖) 1 f

/-- Membership in `ℚ_p⟨z⟩` is Mathlib's restrictedness predicate with radius `1`. -/
theorem mem_tateAlgebra_iff_isRestricted {f : ℚ_[p]⟦X⟧} :
    f ∈ tateAlgebra p ↔ PowerSeries.IsRestricted 1 f :=
  Iff.rfl

/-- A power series lies in `ℚ_p⟨z⟩` iff its coefficients tend to `0`. -/
@[zeta5irr "def_tau_tate"]
theorem mem_tateAlgebra_iff {f : ℚ_[p]⟦X⟧} :
    f ∈ tateAlgebra p ↔ Tendsto (fun d => ‖coeff d f‖) atTop (𝓝 0) := by
  rw [mem_tateAlgebra_iff_isRestricted, PowerSeries.isRestricted_iff']
  simp

/-- The Gauss norm is the supremum of the norms of the coefficients. -/
@[zeta5irr "def_tau_tate"]
theorem tateNorm_eq_iSup (f : ℚ_[p]⟦X⟧) : tateNorm f = ⨆ d, ‖coeff d f‖ := by
  rw [tateNorm, PowerSeries.gaussNorm_eq]
  simp

/-- If every coefficient of `f` has norm at most `C`, then the Gauss norm of `f` is at most
`C`. -/
theorem tateNorm_le_of_forall_norm_coeff_le {f : ℚ_[p]⟦X⟧} {C : ℝ}
    (h : ∀ d, ‖coeff d f‖ ≤ C) : tateNorm f ≤ C := by
  rw [tateNorm_eq_iSup]
  exact ciSup_le h

/-- If every coefficient of the polynomial `U` has norm at most `C`, then the Gauss norm of
`U` is at most `C`. -/
theorem tateNorm_coe_le_of_forall_norm_coeff_le {U : Polynomial ℚ_[p]} {C : ℝ}
    (h : ∀ d, ‖U.coeff d‖ ≤ C) : tateNorm (U : ℚ_[p]⟦X⟧) ≤ C :=
  tateNorm_le_of_forall_norm_coeff_le fun d => by simpa using h d

/-- A polynomial with coefficients in `ℤ_p`, viewed in `ℚ_p⟨z⟩`, has Gauss norm at most `1`. -/
theorem tateNorm_map_coe_le_one (U : Polynomial ℤ_[p]) :
    tateNorm ((U.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) ≤ 1 :=
  tateNorm_coe_le_of_forall_norm_coeff_le fun d => by
    rw [Polynomial.coeff_map]
    exact (U.coeff d).norm_le_one

/-- Every polynomial lies in `ℚ_p⟨z⟩`. -/
theorem coe_mem_tateAlgebra (U : Polynomial ℚ_[p]) : (U : ℚ_[p]⟦X⟧) ∈ tateAlgebra p := by
  rw [mem_tateAlgebra_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop U.natDegree] with d hd
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hd]

/-- The norms of the coefficients of an element of `ℚ_p⟨z⟩` are bounded. -/
theorem bddAbove_range_norm_coeff {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    BddAbove (Set.range fun d => ‖coeff d f‖) :=
  (mem_tateAlgebra_iff.mp hf).bddAbove_range

/-- An element of `ℚ_p⟨z⟩` has a finite Gauss norm of radius `1`. -/
theorem hasGaussNorm {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    PowerSeries.HasGaussNorm (‖·‖) 1 f := by
  simpa [PowerSeries.HasGaussNorm] using bddAbove_range_norm_coeff hf

/-- On `ℚ_p⟨z⟩`, every coefficient has norm at most the Gauss norm. -/
theorem le_tateNorm {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) (d : ℕ) :
    ‖coeff d f‖ ≤ tateNorm f := by
  simpa using PowerSeries.le_gaussNorm _ _ f (hasGaussNorm hf) d

/-- The Gauss norm is non-negative. -/
theorem tateNorm_nonneg (f : ℚ_[p]⟦X⟧) : 0 ≤ tateNorm f :=
  PowerSeries.gaussNorm_nonneg _ _ f fun _ => norm_nonneg _

/-- The Gauss norm of `0` is `0`; this is `‖U‖ = p^{-v_p^G(U)}` for `U = 0`, where
`v_p^G(0) = +∞`. -/
@[zeta5irr "def_tau_tate", simp]
theorem tateNorm_zero : tateNorm (0 : ℚ_[p]⟦X⟧) = 0 :=
  PowerSeries.gaussNorm_zero _ _ norm_zero

/-- On `ℚ_p⟨z⟩`, the Gauss norm vanishes only at `0`. -/
theorem tateNorm_eq_zero_iff {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    tateNorm f = 0 ↔ f = 0 :=
  PowerSeries.gaussNorm_eq_zero_iff _ _ f norm_zero (fun _ => norm_nonneg _)
    (fun _ => norm_eq_zero.mp) one_pos (hasGaussNorm hf)

/-- The ultrametric inequality for the Gauss norm on `ℚ_p⟨z⟩`. -/
theorem tateNorm_add_le_max {f g : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) (hg : g ∈ tateAlgebra p) :
    tateNorm (f + g) ≤ max (tateNorm f) (tateNorm g) :=
  PowerSeries.gaussNorm_add_le_max _ _ f g zero_le_one (fun _ => norm_nonneg _)
    (fun x y => IsUltrametricDist.norm_add_le_max x y) (hasGaussNorm hf) (hasGaussNorm hg)

/-- The Gauss norm is homogeneous: `‖a • f‖ = |a|_p ‖f‖`. -/
theorem tateNorm_smul (a : ℚ_[p]) (f : ℚ_[p]⟦X⟧) : tateNorm (a • f) = ‖a‖ * tateNorm f := by
  simp_rw [tateNorm_eq_iSup, map_smul, smul_eq_mul, norm_mul]
  exact (Real.mul_iSup_of_nonneg (norm_nonneg a) _).symm

/-- The Gauss norm is invariant under negation. -/
theorem tateNorm_neg (f : ℚ_[p]⟦X⟧) : tateNorm (-f) = tateNorm f := by
  simpa using tateNorm_smul (-1 : ℚ_[p]) f

/-- For a polynomial `U ∈ ℚ_p[z]` with Gauss valuation `v_p^G(U) = n`, the Gauss norm of `U` is
`p^{-n}`. -/
@[zeta5irr "def_tau_tate"]
theorem tateNorm_coe_polynomial {U : Polynomial ℚ_[p]} {n : ℤ} (hU : vpG U = n) :
    tateNorm (U : ℚ_[p]⟦X⟧) = (p : ℝ) ^ (-n) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hU0 : U ≠ 0 := by
    rintro rfl
    simp at hU
  -- each coefficient has norm at most `p^{-n}`
  have hle : ∀ d, ‖U.coeff d‖ ≤ (p : ℝ) ^ (-n) := by
    intro d
    by_cases hd : U.coeff d = 0
    · rw [hd, norm_zero]
      positivity
    have hv := gaussAddVal_le Padic.addValuation U d
    rw [show gaussAddVal Padic.addValuation U = vpG U from rfl, hU,
      Padic.addValuation.apply hd, WithTop.coe_le_coe] at hv
    rw [Padic.norm_eq_zpow_neg_valuation hd]
    exact zpow_le_zpow_right₀ hp.le (neg_le_neg hv)
  obtain ⟨j, hj, hjv⟩ := exists_gaussAddVal_eq Padic.addValuation hU0
  have hj0 : U.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hjn : ‖U.coeff j‖ = (p : ℝ) ^ (-n) := by
    rw [show gaussAddVal Padic.addValuation U = vpG U from rfl, hU,
      Padic.addValuation.apply hj0, WithTop.coe_inj] at hjv
    rw [Padic.norm_eq_zpow_neg_valuation hj0, hjv]
  refine le_antisymm ?_ ?_
  · exact tateNorm_coe_le_of_forall_norm_coeff_le hle
  · simpa [hjn] using le_tateNorm (coe_mem_tateAlgebra U) j

end Zeta5Irr
