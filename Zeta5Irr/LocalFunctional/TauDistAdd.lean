/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDist
public import Zeta5Irr.LocalFunctional.TauFarMem
public import Zeta5Irr.LocalFunctional.LocalDeltaConv
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Zeta5Irr.LocalFunctional.KappaVal

/-!
# Additivity of the distributed functional `𝒯_p(-; R)`

Let `p` be a prime and `R ⊆ ℤ` finite. The distributed functional
`𝒯_p(A; R) = p^{-4} ∑_{a=0}^{p-1} τ_{Y_p}^ext(δ_{R_a}^ext(p^{-#R} A(a + pz) ∏_{s ∈ Σ_a} ε_s))`
is additive in `A ∈ ℚ[x]`.

Every ingredient is additive on the Tate algebra `𝒜 = ℚ_p⟨z⟩`: the substitution
`A ↦ A(a + pz)` and multiplication by the fixed element `p^{-#R} ∏_{s ∈ Σ_a} ε_s ∈ 𝒜`;
the extended near-pole decomposition `δ_{R_a}^ext`, a limit of the additive maps
`δ_{R_a}(f^{[D]})` which converge on `𝒜`; and `τ_Y^ext`, whose analytic part
`τ^an(f) = ∑_d f_d κ_d` converges on `𝒜`.

## Main results

* `Zeta5Irr.norm_kappa_le_mul`: `|κ_d|_p ≤ p |1/24|_p` for every prime `p`.
* `Zeta5Irr.summable_coeff_mul_kappa_of_mem`: `∑_d f_d κ_d` converges for `f ∈ 𝒜`, for every
  prime `p`.
* `Zeta5Irr.tauAn_add`, `Zeta5Irr.tauExt_add`, `Zeta5Irr.deltaExt_add`: additivity of the
  ingredients.
* `Zeta5Irr.tauDist_add`: `𝒯_p(A₁ + A₂; R) = 𝒯_p(A₁; R) + 𝒯_p(A₂; R)`.

## Implementation notes

The source proves convergence of `∑_d f_d κ_d` on `𝒜` only for `p ≥ 5`, where `|κ_d|_p ≤ p`.
For `p = 2, 3` the weights are still bounded, `|κ_d|_p ≤ p |1/24|_p`, because `v_p(B_n) ≥ -1`
holds for every prime; so the series converges on `𝒜` for every prime and the additivity
holds as stated, for every prime `p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- For every prime `p` and every `d`, `|κ_d|_p ≤ p |1/24|_p`. -/
theorem norm_kappa_le_mul (d : ℕ) :
    ‖(kappa d : ℚ_[p])‖ ≤ p * ‖((24 : ℚ_[p]))⁻¹‖ := by
  rw [kappa, div_eq_mul_inv]
  push_cast
  rw [norm_mul, norm_mul]
  gcongr
  calc ‖((d.descFactorial 3 : ℕ) : ℚ_[p])‖ * ‖((_root_.bernoulli (d - 3) : ℚ) : ℚ_[p])‖
      ≤ 1 * p := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
        · exact norm_bernoulli_le _
    _ = p := one_mul _

/-- **Convergence of `∑ f_d κ_d` for every prime.** For `f ∈ ℚ_p⟨z⟩`, the series
`∑_{d ≥ 0} f_d κ_d` converges in `ℚ_p`. -/
theorem summable_coeff_mul_kappa_of_mem {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    Summable fun d => coeff d f * (kappa d : ℚ_[p]) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have h := (mem_tateAlgebra_iff.mp hf).mul_const ((p : ℝ) * ‖((24 : ℚ_[p]))⁻¹‖)
  rw [zero_mul] at h
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_kappa_le_mul d) (norm_nonneg _)

/-- `τ^an` is additive on `ℚ_p⟨z⟩`: `τ^an(f + g) = τ^an(f) + τ^an(g)`. -/
theorem tauAn_add {f g : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) (hg : g ∈ tateAlgebra p) :
    tauAn (f + g) = tauAn f + tauAn g := by
  simp only [tauAn, map_add, add_mul]
  exact (summable_coeff_mul_kappa_of_mem hf).tsum_add (summable_coeff_mul_kappa_of_mem hg)

/-- `τ_Y^ext` is additive on `𝓑_R`: `τ_Y^ext(x + y) = τ_Y^ext(x) + τ_Y^ext(y)`. -/
theorem tauExt_add {R : Finset ℤ} (Y : Polynomial ℚ_[p]) (x y : BT p R) :
    tauExt R Y (x + y) = tauExt R Y x + tauExt R Y y := by
  have h : tauAn ((x + y).fst : ℚ_[p]⟦X⟧) =
      tauAn (x.fst : ℚ_[p]⟦X⟧) + tauAn (y.fst : ℚ_[p]⟦X⟧) :=
    tauAn_add x.fst.2 y.fst.2
  simp only [tauExt, h, Polynomial.C_add]
  change _ + ∑ r : R, (x.res r + y.res r) • _ = _
  simp only [add_smul, Finset.sum_add_distrib]
  ring

/-- `δ_R^ext` is additive on `ℚ_p⟨z⟩`: `δ_R^ext(f + g) = δ_R^ext(f) + δ_R^ext(g)`. -/
theorem deltaExt_add {R : Finset ℤ} {f g : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p)
    (hg : g ∈ tateAlgebra p) : deltaExt R (f + g) = deltaExt R f + deltaExt R g := by
  refine deltaExt_eq_of_tendsto ?_
  simp only [map_add, deltaR_add]
  exact (tendsto_deltaR_trunc_deltaExt hf).add (tendsto_deltaR_trunc_deltaExt hg)

/-- **Additivity of `𝒯_p`.** For every prime `p`, finite `R ⊆ ℤ` and `A₁, A₂ ∈ ℚ[x]`,
`𝒯_p(A₁ + A₂; R) = 𝒯_p(A₁; R) + 𝒯_p(A₂; R)`. -/
@[zeta5irr "lem_tau_dist_add"]
theorem tauDist_add (R : Finset ℤ) (A₁ A₂ : Polynomial ℚ) :
    tauDist p R (A₁ + A₂) = tauDist p R A₁ + tauDist p R A₂ := by
  simp only [tauDist, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← tauExt_add]
  congr 1
  set F := ∏ s ∈ distFarPoles p R a, farEps s
  set c : ℚ_[p] := ((p : ℚ_[p]) ^ R.card)⁻¹
  have hmem : ∀ A : Polynomial ℚ, c • ((((A.comp (Polynomial.C (a : ℚ) +
      Polynomial.C (p : ℚ) * Polynomial.X)).map
      (algebraMap ℚ ℚ_[p]) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) * F) ∈ tateAlgebra p := by
    intro A
    rw [← mul_smul_comm]
    exact Subalgebra.mul_mem _ (coe_mem_tateAlgebra _)
      (Subalgebra.smul_mem _ (prod_farEps_mem_tateAlgebra R a) c)
  rw [← deltaExt_add (hmem A₁) (hmem A₂)]
  congr 1
  simp only [Polynomial.add_comp, Polynomial.map_add, Polynomial.coe_add, add_mul, smul_add]

end Zeta5Irr
