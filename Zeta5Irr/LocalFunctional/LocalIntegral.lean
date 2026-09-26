/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.HarmonicFivePadicInt
public import Zeta5Irr.LocalFunctional.LocalAnalyticInt
public import Zeta5Irr.LocalFunctional.LocalDeltaDiv
public import Zeta5Irr.LocalFunctional.LocalDeltaNorm

/-!
# The local integrality lemma

Let `p ≥ 5` be a prime and `R ⊆ ℤ` finite, with `r - r'` a `p`-adic unit for distinct
`r, r' ∈ R` and `d(r) < p` for `r ∈ R`, and let `Y ∈ ℤ_p[X]`. Let `U_j ∈ ℤ_p[z]` with
`deg U_0 ≤ p + 1`, and suppose `q ∈ 𝒜 = ℚ_p⟨z⟩` and `b ∈ ℚ_p[z]` with `deg b < #R` satisfy
`∑_{j ≥ 0} p^j U_j = q E_R + b` in `𝒜`. Then
`τ_Y^ext(q, (b(r) / E_R'(r))_{r ∈ R}) ∈ ℤ_p[X]`.

By definition the value is `τ^an(q) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - Y)` with
`c_r = b(r) / E_R'(r)`. The analytic term `τ^an(q)` is a `p`-adic integer. The pair
`(q, (c_r))` is `δ_R^ext(q E_R + b)`, and `‖q E_R + b‖ ≤ 1` since it is a limit of the partial
sums `∑_{j < J} p^j U_j`, whose coefficients are `p`-adic integers; as `δ_R^ext` does not
increase norms, `|c_r|_p ≤ 1`. Finally `H_{d(r)}^{(5)} ∈ ℤ_p` because `d(r) < p`.

## Main results

* `Zeta5Irr.tateNorm_le_one_of_tendsto`: `‖q E_R + b‖ ≤ 1`, in the more general form that a
  limit of the partial sums `∑_{j < J} p^j U_j` has Gauss norm at most `1`.
* `Zeta5Irr.tauExt_mem_lifts_of_tendsto`: the local integrality lemma,
  `τ_Y^ext(q, (b(r) / E_R'(r))_{r ∈ R}) ∈ ℤ_p[X]`.

## Implementation notes

* Membership in `ℤ_p[X]` is stated as membership in `Polynomial.lifts` of the inclusion
  `ℤ_p → ℚ_p`, and the hypothesis `∑_{j ≥ 0} p^j U_j = q E_R + b` in `𝒜` as convergence of
  the partial sums to `q E_R + b` in the Gauss norm.
* The source assumes `p ≥ 7` and `R ≠ ∅`; the argument uses only `p ≥ 5`, which is what the
  integrality of `τ^an(q)` requires, and does not use `R ≠ ∅`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime), Lemma 3.1.
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- A limit in `ℚ_p⟨z⟩` of the partial sums `∑_{j < J} p^j U_j` of `p`-adically scaled
polynomials `U_j ∈ ℤ_p[z]` has Gauss norm at most `1`. -/
theorem tateNorm_le_one_of_tendsto (U : ℕ → Polynomial ℤ_[p]) {g : ℚ_[p]⟦X⟧}
    (hg : g ∈ tateAlgebra p)
    (h : Tendsto (fun J => tateNorm (∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) - g)) atTop (𝓝 0)) :
    tateNorm g ≤ 1 := by
  obtain ⟨J, hJ⟩ := (h.eventually (ge_mem_nhds zero_lt_one)).exists
  set S := ∑ j ∈ range J, (p : ℚ_[p]) ^ j •
    (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) with hS
  have hSmem : S ∈ tateAlgebra p :=
    sum_mem fun j _ => Subalgebra.smul_mem _ (coe_mem_tateAlgebra _) _
  have hSn : ∀ n, coeff n S =
      ((∑ j ∈ range J, (p : ℤ_[p]) ^ j * (U j).coeff n : ℤ_[p]) : ℚ_[p]) := by
    intro n
    simp [hS, map_sum, Polynomial.coeff_coe]
    rfl
  refine tateNorm_le_of_forall_norm_coeff_le fun n => ?_
  have hsplit : coeff n g = coeff n S + -coeff n (S - g) := by
    rw [map_sub]; ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [hSn]
    exact PadicInt.norm_le_one _
  · rw [norm_neg]
    exact (le_tateNorm (sub_mem hSmem hg) n).trans hJ

/-- **The local integrality lemma.** Let `p ≥ 5` be a prime and `R ⊆ ℤ` finite, with `r - r'`
a `p`-adic unit for distinct `r, r' ∈ R` and `d(r) < p` for `r ∈ R`, and let `Y ∈ ℤ_p[X]`.
Let `U_j ∈ ℤ_p[z]` with `deg U_0 ≤ p + 1`, and let `q ∈ ℚ_p⟨z⟩`, `b ∈ ℚ_p[z]` with
`deg b < #R` satisfy `∑_{j ≥ 0} p^j U_j = q E_R + b` in `ℚ_p⟨z⟩`. Then
`τ_Y^ext(q, (b(r) / E_R'(r))_{r ∈ R}) ∈ ℤ_p[X]`. -/
@[zeta5irr "lem_local_integral"]
theorem tauExt_mem_lifts_of_tendsto (hp5 : 5 ≤ p) {R : Finset ℤ}
    (hR : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → IsUnit ((r - r' : ℤ) : ℤ_[p]))
    (hRp : ∀ r ∈ R, reflectIndex r < p) {Y : Polynomial ℚ_[p]}
    (hY : Y ∈ lifts (PadicInt.Coe.ringHom (p := p))) (U : ℕ → Polynomial ℤ_[p])
    (hU0 : (U 0).natDegree ≤ p + 1) (q : tateAlgebra p) {b : Polynomial ℚ_[p]}
    (hb : b.degree < #R)
    (h : Tendsto (fun J => tateNorm (∑ j ∈ range J, (p : ℚ_[p]) ^ j •
      (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) -
        ((q : ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧)))) atTop
      (𝓝 0)) :
    tauExt R Y (BT.mk q fun r => b.eval ((r : ℤ) : ℚ_[p]) /
        (derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  set c : R → ℚ_[p] := fun r => b.eval ((r : ℤ) : ℚ_[p]) /
    (derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p]) with hc
  set ι : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  -- the residues are `p`-adic integers
  have hgmem : (q : ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧) ∈
      tateAlgebra p :=
    add_mem (mul_mem q.2 (coe_mem_tateAlgebra _)) (coe_mem_tateAlgebra b)
  have hres : ∀ r, ‖c r‖ ≤ 1 := by
    intro r
    have hδ := norm_deltaExt_le_norm hR ⟨_, hgmem⟩
    rw [deltaExt_eq_of_eq_mul_add hb rfl, tateAlgebra.norm_def] at hδ
    have hle := hδ.trans (tateNorm_le_one_of_tendsto U hgmem h)
    rw [BT.norm_mk] at hle
    exact (le_ciSup (f := fun r => ‖c r‖) (Finite.bddAbove_range _) r).trans
      ((le_max_right _ _).trans hle)
  rw [lifts_iff_liftsRing, tauExt_mk]
  refine add_mem ?_ (sum_mem fun r _ => ?_)
  · obtain ⟨x, hx⟩ := exists_padicInt_eq_tauAn_of_tendsto hp5 R U hU0 q.2 hb h
    rw [← lifts_iff_liftsRing, ← hx]
    exact C_mem_lifts ι x
  · obtain ⟨x, hx⟩ := exists_padicInt_eq_harmonicFive (hRp r r.2)
    rw [Polynomial.smul_eq_C_mul]
    refine mul_mem ?_ (sub_mem ?_ ((lifts_iff_liftsRing _ _).mp hY))
    · rw [← lifts_iff_liftsRing]
      exact C_mem_lifts ι ⟨c r, hres r⟩
    · rw [← lifts_iff_liftsRing, ← hx]
      exact C_mem_lifts ι x

end Zeta5Irr
