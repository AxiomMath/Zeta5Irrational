/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauFar
public import Zeta5Irr.LocalFunctional.TauTate
public import Mathlib.Algebra.Order.Star.Real

/-!
# The far-pole series `ε_s` lies in the Tate algebra

For `s ∈ ℚ_p` with `v_p(s) < 0`, the power series `ε_s = -∑_{k ≥ 0} s^{-k-1} z^k` lies in the
Tate algebra `𝒜 = ℚ_p⟨z⟩`, and its Gauss norm is `‖ε_s‖ = |s⁻¹|_p < 1`. Indeed the `k`-th
coefficient of `ε_s` has norm `|s⁻¹|_p^{k+1}`, and `|s⁻¹|_p = p^{v_p(s)} < 1`, so these norms
tend to `0` and their supremum is attained at `k = 0`.

## Main results

* `Zeta5Irr.norm_inv_lt_one_of_valuation_neg`: `v_p(s) < 0` implies `|s⁻¹|_p < 1`.
* `Zeta5Irr.farEps_mem_tateAlgebra`, `Zeta5Irr.tateNorm_farEps`: for `|s⁻¹|_p < 1`,
  `ε_s ∈ ℚ_p⟨z⟩` and `‖ε_s‖ = |s⁻¹|_p`.
* `Zeta5Irr.farEps_mem_tateAlgebra_and_tateNorm`: the statement of the source, for `v_p(s) < 0`.

## Implementation notes

* The membership and norm statements are proved under the hypothesis `|s⁻¹|_p < 1`, which is
  equivalent to `v_p(s) < 0`; the source's form, with `v_p(s) < 0`, is derived from them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime]

/-- If `v_p(s) < 0` then `|s⁻¹|_p = p^{v_p(s)} < 1`. -/
theorem norm_inv_lt_one_of_valuation_neg {s : ℚ_[p]} (hs : s.valuation < 0) : ‖s⁻¹‖ < 1 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation hs0, ← zpow_neg, neg_neg]
  exact zpow_lt_one_of_neg₀ hp hs

/-- The norms of the coefficients of `ε_s` are `|s⁻¹|_p^{k+1}`. -/
theorem norm_coeff_farEps (s : ℚ_[p]) (k : ℕ) : ‖coeff k (farEps s)‖ = ‖s⁻¹‖ ^ (k + 1) := by
  rw [coeff_farEps, norm_neg, norm_pow]

/-- If `|s⁻¹|_p < 1`, then `ε_s` lies in the Tate algebra `ℚ_p⟨z⟩`. -/
theorem farEps_mem_tateAlgebra {s : ℚ_[p]} (hs : ‖s⁻¹‖ < 1) : farEps s ∈ tateAlgebra p := by
  rw [mem_tateAlgebra_iff]
  simp_rw [norm_coeff_farEps]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hs).comp (tendsto_add_atTop_nat 1)

/-- If `|s⁻¹|_p < 1`, then the Gauss norm of `ε_s` is `|s⁻¹|_p`. -/
theorem tateNorm_farEps {s : ℚ_[p]} (hs : ‖s⁻¹‖ < 1) : tateNorm (farEps s) = ‖s⁻¹‖ := by
  refine le_antisymm ?_ ?_
  · refine tateNorm_le_of_forall_norm_coeff_le fun k => ?_
    rw [norm_coeff_farEps]
    exact pow_le_of_le_one (norm_nonneg _) hs.le k.succ_ne_zero
  · simpa [norm_coeff_farEps] using le_tateNorm (farEps_mem_tateAlgebra hs) 0

/-- For `s ∈ ℚ_p` with `v_p(s) < 0`, `ε_s ∈ ℚ_p⟨z⟩` and `‖ε_s‖ = |s⁻¹|_p < 1`. -/
@[zeta5irr "lem_tau_far_mem"]
theorem farEps_mem_tateAlgebra_and_tateNorm {s : ℚ_[p]} (hs : s.valuation < 0) :
    farEps s ∈ tateAlgebra p ∧ tateNorm (farEps s) = ‖s⁻¹‖ ∧ ‖s⁻¹‖ < 1 :=
  have h := norm_inv_lt_one_of_valuation_neg hs
  ⟨farEps_mem_tateAlgebra h, tateNorm_farEps h, h⟩

end Zeta5Irr
