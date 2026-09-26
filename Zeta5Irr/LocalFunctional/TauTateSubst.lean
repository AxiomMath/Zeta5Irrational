/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauTate
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Affine substitution in the Tate algebra `ℚ_p⟨z⟩`

For a power series `f = ∑_{d ≥ 0} f_d z^d ∈ ℚ_p[[z]]` and `u, c ∈ ℚ_p`, the formal substitution
`f(u + cz) = ∑_{d ≥ 0} f_d (u + cz)^d` is formed coefficientwise: its coefficient of `z^m` is the
`p`-adic series `∑_{d ≥ 0} f_d [z^m](u + cz)^d = ∑_{d ≥ m} f_d \binom{d}{m} c^m u^{d-m}`.
When `f ∈ ℚ_p⟨z⟩` and `|u|_p, |c|_p ≤ 1` (in particular for `u, c ∈ ℤ_p`), every coefficient
`\binom{d}{m} c^m u^{d-m}` has absolute value at most `1`, so these series converge, the result
again lies in `ℚ_p⟨z⟩`, and by the ultrametric inequality `‖f(u + cz)‖ ≤ ‖f‖`.

## Main definitions

* `Zeta5Irr.tateSubst u c f`: the coefficientwise substitution `f(u + cz)`.

## Main results

* `Zeta5Irr.coeff_add_mul_X_pow`: `[z^m](u + cz)^d = \binom{d}{m} c^m u^{d-m}` for `m ≤ d`, and `0`
  otherwise.
* `Zeta5Irr.hasSum_coeff_tateSubst`: for `f ∈ ℚ_p⟨z⟩` and `|u|_p, |c|_p ≤ 1`, the series defining
  each coefficient of `f(u + cz)` converges.
* `Zeta5Irr.tateSubst_mem_tateAlgebra`: `f(u + cz) ∈ ℚ_p⟨z⟩`.
* `Zeta5Irr.tateNorm_tateSubst_le`: `‖f(u + cz)‖ ≤ ‖f‖`.

## Implementation notes

* The source takes `u, c ∈ ℤ_p`; we take `u, c ∈ ℚ_p` with `|u|_p ≤ 1` and `|c|_p ≤ 1`, which is
  the same condition, and avoids coercions from `ℤ_p` when the result is applied.
* `Mathlib`'s `PowerSeries.subst` does not apply, since the constant term `u` of `u + cz` need not
  be nilpotent; the substitution is instead defined coefficientwise through `tsum`. The
  definition makes sense for all `f`, `u`, `c`, with junk values where the series diverge.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- The coefficientwise affine substitution `f(u + cz) = ∑_{d ≥ 0} f_d (u + cz)^d` of a power
series `f ∈ ℚ_p[[z]]`: its coefficient of `z^m` is the `p`-adic sum
`∑_{d ≥ 0} f_d [z^m](u + cz)^d`. -/
@[zeta5irr "lem_tau_tate_subst"]
noncomputable def tateSubst (u c : ℚ_[p]) (f : ℚ_[p]⟦X⟧) : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun m => ∑' d, coeff d f * coeff m ((C u + C c * X) ^ d)

/-- The coefficient of `z^m` in `f(u + cz)` is `∑_{d ≥ 0} f_d [z^m](u + cz)^d`. -/
theorem coeff_tateSubst (u c : ℚ_[p]) (f : ℚ_[p]⟦X⟧) (m : ℕ) :
    coeff m (tateSubst u c f) = ∑' d, coeff d f * coeff m ((C u + C c * X) ^ d) :=
  coeff_mk _ _

/-- The binomial theorem for `u + cz`: the coefficient of `z^m` in `(u + cz)^d` is
`\binom{d}{m} c^m u^{d-m}` for `m ≤ d` and `0` otherwise. -/
theorem coeff_add_mul_X_pow {R : Type*} [CommRing R] (u c : R) (d m : ℕ) :
    coeff m ((C u + C c * X) ^ d) =
      if m ≤ d then (d.choose m : R) * c ^ m * u ^ (d - m) else 0 := by
  have h : ∀ k ∈ Finset.range (d + 1), (C c * X) ^ k * C u ^ (d - k) * (d.choose k : R⟦X⟧) =
      C ((d.choose k : R) * c ^ k * u ^ (d - k)) * X ^ k := by
    intro k _
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [add_comm, add_pow, Finset.sum_congr rfl h, map_sum]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- For `|u|_p, |c|_p ≤ 1`, every coefficient of `(u + cz)^d` has `p`-adic absolute value at
most `1`. -/
theorem norm_coeff_add_mul_X_pow_le_one {u c : ℚ_[p]} (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1) (d m : ℕ) :
    ‖coeff m ((C u + C c * X) ^ d)‖ ≤ 1 := by
  rw [coeff_add_mul_X_pow]
  split_ifs
  · have hd : ‖(d.choose m : ℚ_[p])‖ ≤ 1 := by
      simpa using Padic.norm_int_le_one (p := p) (d.choose m : ℤ)
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖(d.choose m : ℚ_[p])‖ * ‖c‖ ^ m * ‖u‖ ^ (d - m) ≤ 1 * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hc
          · exact pow_le_one₀ (norm_nonneg _) hu
      _ = 1 := by norm_num
  · simp

/-- Each term `f_d [z^m](u + cz)^d` of the series defining a coefficient of `f(u + cz)` has
absolute value at most `|f_d|_p`, and vanishes for `d < m`. -/
private theorem norm_term_le {u c : ℚ_[p]} (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1) (f : ℚ_[p]⟦X⟧)
    (d m : ℕ) : ‖coeff d f * coeff m ((C u + C c * X) ^ d)‖ ≤ ‖coeff d f‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_coeff_add_mul_X_pow_le_one hu hc d m)

private theorem term_eq_zero (u c : ℚ_[p]) (f : ℚ_[p]⟦X⟧) {d m : ℕ} (h : d < m) :
    coeff d f * coeff m ((C u + C c * X) ^ d) = 0 := by
  simp [coeff_add_mul_X_pow, show ¬m ≤ d by omega]

/-- For `f ∈ ℚ_p⟨z⟩` and `|u|_p, |c|_p ≤ 1`, the `p`-adic series defining the coefficient of
`z^m` in `f(u + cz)` converges. -/
theorem hasSum_coeff_tateSubst {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) {u c : ℚ_[p]}
    (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1) (m : ℕ) :
    HasSum (fun d => coeff d f * coeff m ((C u + C c * X) ^ d)) (coeff m (tateSubst u c f)) := by
  rw [coeff_tateSubst]
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun d => norm_term_le hu hc f d m)
    (mem_tateAlgebra_iff.mp hf)

/-- If `|f_d|_p ≤ ε` for all `d ≥ m`, then the coefficient of `z^m` in `f(u + cz)` has absolute
value at most `ε`. -/
private theorem norm_coeff_tateSubst_le {u c : ℚ_[p]} (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (f : ℚ_[p]⟦X⟧) {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ d, m ≤ d → ‖coeff d f‖ ≤ ε) :
    ‖coeff m (tateSubst u c f)‖ ≤ ε := by
  rw [coeff_tateSubst]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun d => ?_
  rcases lt_or_ge d m with hd | hd
  · rw [term_eq_zero u c f hd, norm_zero]
    exact hε
  · exact (norm_term_le hu hc f d m).trans (h d hd)

/-- **Affine substitution in `ℚ_p⟨z⟩`.** For `f ∈ ℚ_p⟨z⟩` and `|u|_p, |c|_p ≤ 1`, the formal
substitution `f(u + cz)` lies in `ℚ_p⟨z⟩`. -/
@[zeta5irr "lem_tau_tate_subst"]
theorem tateSubst_mem_tateAlgebra {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) {u c : ℚ_[p]}
    (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1) : tateSubst u c f ∈ tateAlgebra p := by
  rw [mem_tateAlgebra_iff]
  have hf' := mem_tateAlgebra_iff.mp hf
  rw [Metric.tendsto_atTop] at hf' ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf' (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine (norm_coeff_tateSubst_le hu hc f (half_pos hε).le fun d hd => ?_).trans_lt
    (half_lt_self hε)
  have := hN d (hm.trans hd)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  exact this.le

/-- **Affine substitution in `ℚ_p⟨z⟩` does not increase the Gauss norm.** For `f ∈ ℚ_p⟨z⟩` and
`|u|_p, |c|_p ≤ 1`, `‖f(u + cz)‖ ≤ ‖f‖`. -/
@[zeta5irr "lem_tau_tate_subst"]
theorem tateNorm_tateSubst_le {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) {u c : ℚ_[p]}
    (hu : ‖u‖ ≤ 1) (hc : ‖c‖ ≤ 1) : tateNorm (tateSubst u c f) ≤ tateNorm f := by
  exact tateNorm_le_of_forall_norm_coeff_le fun m =>
    norm_coeff_tateSubst_le hu hc f (tateNorm_nonneg f) fun d _ => le_tateNorm hf d

end Zeta5Irr
