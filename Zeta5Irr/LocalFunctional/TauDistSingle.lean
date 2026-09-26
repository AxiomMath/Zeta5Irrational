/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDist
public import Zeta5Irr.LocalFunctional.TauDistval
public import Zeta5Irr.LocalFunctional.LocalCompat
public import Zeta5Irr.LocalFunctional.TauFarMem

/-!
# The distributed functional of a single pole

Let `p` be a prime and `r ∈ ℤ`. For the single pole `R = {r}` and `A = 1`, the distributed
functional is an average of local pole values:
`𝒯_p(1; {r}) = p^{-5} ∑_{a=0}^{p-1} w_p(r - a)`.

For each residue `a`, exactly one of the two pole sets is nonempty. If `p ∣ r - a` then
`R_a = {ρ}` with `ρ = (r - a) / p` and `Σ_a = ∅`; the argument of `δ_{R_a}^ext` is the constant
`p^{-1}`, whose decomposition is `(0, (p^{-1}))`, and the `a`th summand is
`p^{-1} (H_{d(ρ)}^{(5)} - Y_p) = p^{-1} w_p(r - a)`. If `p ∤ r - a` then `R_a = ∅` and
`Σ_a = {s}` with `s = (r - a) / p`; the argument is `p^{-1} ε_s`, whose decomposition is
`(p^{-1} ε_s, ())`, and the `a`th summand is `p^{-1} τ^an(ε_s) = p^{-1} w_p(r - a)`.
Both decompositions are instances of the compatibility of `δ^ext` with partial fractions.

## Main results

* `Zeta5Irr.distNearPoles_singleton_of_dvd`, `Zeta5Irr.distFarPoles_singleton_of_dvd`,
  `Zeta5Irr.distNearPoles_singleton_of_not_dvd`, `Zeta5Irr.distFarPoles_singleton_of_not_dvd`:
  the pole sets `R_a` and `Σ_a` of a single pole.
* `Zeta5Irr.tauDist_singleton_one`: `𝒯_p(1; {r}) = p^{-5} ∑_{a=0}^{p-1} w_p(r - a)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ}

/-- If `p ∣ r - a`, the single pole `r` stays integral: `R_a = {(r - a) / p}`. -/
theorem distNearPoles_singleton_of_dvd {r : ℤ} {a : ℕ} (h : (p : ℤ) ∣ r - a) :
    distNearPoles p {r} a = {(r - a) / p} := by
  have : r ≡ a [ZMOD p] := (Int.modEq_iff_dvd.mpr h).symm
  simp [distNearPoles, Finset.filter_singleton, this]

/-- If `p ∤ r - a`, the single pole `r` contributes no integral pole: `R_a = ∅`. -/
theorem distNearPoles_singleton_of_not_dvd {r : ℤ} {a : ℕ} (h : ¬(p : ℤ) ∣ r - a) :
    distNearPoles p {r} a = ∅ := by
  have : ¬r ≡ a [ZMOD p] := fun h' => h (Int.modEq_iff_dvd.mp h'.symm)
  simp [distNearPoles, Finset.filter_singleton, this]

variable [Fact p.Prime]

/-- If `p ∣ r - a`, the single pole `r` contributes no far pole: `Σ_a = ∅`. -/
theorem distFarPoles_singleton_of_dvd {r : ℤ} {a : ℕ} (h : (p : ℤ) ∣ r - a) :
    distFarPoles p {r} a = ∅ := by
  have : r ≡ a [ZMOD p] := (Int.modEq_iff_dvd.mpr h).symm
  simp [distFarPoles, Finset.filter_singleton, this]

/-- If `p ∤ r - a`, the single pole `r` moves away: `Σ_a = {(r - a) / p}`. -/
theorem distFarPoles_singleton_of_not_dvd {r : ℤ} {a : ℕ} (h : ¬(p : ℤ) ∣ r - a) :
    distFarPoles p {r} a = {((r - a : ℤ) : ℚ_[p]) / p} := by
  have : ¬r ≡ a [ZMOD p] := fun h' => h (Int.modEq_iff_dvd.mp h'.symm)
  simp [distFarPoles, Finset.filter_singleton, this]

/-- **`𝒯_p(1; {r}) = p^{-5} ∑_{a=0}^{p-1} w_p(r - a)`.** The distributed functional of a
single pole `r ∈ ℤ` with numerator `1` is `p^{-5}` times the sum of the local pole values
`w_p(r - a)` over the residues `0 ≤ a ≤ p - 1`. -/
@[zeta5irr "lem_tau_dist_single"]
theorem tauDist_singleton_one (r : ℤ) :
    tauDist p {r} 1 =
      ((p : ℚ_[p]) ^ 5)⁻¹ • ∑ a ∈ Finset.range p, localPoleValue p (r - a) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [tauDist, show ((p : ℚ_[p]) ^ 5)⁻¹ = ((p : ℚ_[p]) ^ 4)⁻¹ * (p : ℚ_[p])⁻¹ by
    rw [pow_succ, mul_inv], mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.card_singleton, pow_one, one_comp, Polynomial.map_one, Polynomial.coe_one,
    one_mul]
  have hC : ((p : ℚ_[p])⁻¹ • (∏ s ∈ distFarPoles p {r} a, farEps s : PowerSeries ℚ_[p])) =
      ((C (p : ℚ_[p])⁻¹ : ℚ_[p][X]) : PowerSeries ℚ_[p]) *
        ∏ s ∈ distFarPoles p {r} a, farEps s := by
    rw [Polynomial.coe_C, PowerSeries.smul_eq_C_mul]
  rw [hC]
  by_cases h : (p : ℤ) ∣ r - a
  · rw [distFarPoles_singleton_of_dvd h, distNearPoles_singleton_of_dvd h,
      localPoleValue_of_dvd h]
    rw [deltaExt_mul_prod_farEps (S := ∅) (by simp) (P := 0) (c := fun _ => (p : ℚ_[p])⁻¹)
      (e := 0) (q := 0) ?_ (by simp)]
    · rw [tauExt_mk]
      simp [tauAn_zero]
    · simp [intPoleProduct_empty]
  · rw [distFarPoles_singleton_of_not_dvd h, distNearPoles_singleton_of_not_dvd h,
      localPoleValue_of_not_dvd h]
    have hv := valuation_intCast_div_prime h
    have hneg : (((r - a : ℤ) : ℚ_[p]) / p).valuation < 0 := by rw [hv]; exact neg_one_lt_zero
    have hmem := (farEps_mem_tateAlgebra_and_tateNorm hneg).1
    rw [deltaExt_mul_prod_farEps (R := ∅) (S := {((r - a : ℤ) : ℚ_[p]) / p})
      (fun s hs => by rw [Finset.mem_singleton.mp hs]; exact hneg) (P := 0) (c := 0)
      (e := fun _ => (p : ℚ_[p])⁻¹) (q := (p : ℚ_[p])⁻¹ • ⟨_, hmem⟩) ?_ ?_]
    · rw [tauExt_mk]
      simp [tauAn_smul, Polynomial.smul_C]
    · simp [intPoleProduct_empty]
    · simp [PowerSeries.smul_eq_C_mul]

end Zeta5Irr
