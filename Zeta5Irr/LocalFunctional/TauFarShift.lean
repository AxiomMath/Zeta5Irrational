/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauFarMem
public import Zeta5Irr.LocalFunctional.TauTateSubst
public import Mathlib.NumberTheory.Padics.LocalField
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Shifting the far-pole series `ε_s`

For `s ∈ ℚ_p` with `v_p(s) < 0`, the substitution `z ↦ z + 1` carries the far-pole series
`ε_s = -∑_{k ≥ 0} s^{-k-1} z^k`, the expansion of `1 / (z - s)`, to `ε_{s-1}`, the expansion of
`1 / (z + 1 - s)`:
`ε_s(z + 1) = ε_{s-1}`.

## Main results

* `Zeta5Irr.tateSubst_farEps`: more generally `ε_s(u + cz) = c⁻¹ ε_{(s-u)/c}` for `|u|_p ≤ 1`,
  `|c|_p = 1` and `|s|_p > 1`.
* `Zeta5Irr.tateSubst_one_one_farEps`: `ε_s(z + 1) = ε_{s-1}` for `|s|_p > 1`.
* `Zeta5Irr.tateSubst_one_one_farEps_of_valuation_neg`: the statement of the source, for
  `v_p(s) < 0`, via `Zeta5Irr.one_lt_norm_of_valuation_neg`.

## Implementation notes

* The source argues by uniqueness of inverses: substitution is a ring homomorphism, so
  `(z - (s - 1)) ε_s(z + 1) = 1 = (z - (s - 1)) ε_{s-1}`. Here the substitution `tateSubst` is
  defined coefficientwise, and rather than establishing its multiplicativity we compare
  coefficients directly. Writing `t = s⁻¹`, the coefficient of `z^m` in `ε_s(u + cz)` is
  `-∑_{d ≥ m} \binom{d}{m} c^m u^{d-m} t^{d+1} = -c^m t^{m+1} / (1 - tu)^{m+1}`, by the
  negative binomial series, and `c t / (1 - t u) = ((s - u) / c)⁻¹`.
* The main statement is proved under `1 < |s|_p`, which is equivalent to `v_p(s) < 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- If `v_p(s) < 0` then `|s|_p > 1`. -/
theorem one_lt_norm_of_valuation_neg {s : ℚ_[p]} (hs : s.valuation < 0) : 1 < ‖s‖ := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hs0]
  exact one_lt_zpow₀ hp (neg_pos.mpr hs)

/-- For `‖u‖_p ≤ 1`, `‖c‖_p = 1` and `|s|_p > 1`, the substitution `z ↦ u + cz` carries `ε_s`
to `c⁻¹ ε_{(s-u)/c}`, since `1 / (u + cz - s) = c⁻¹ / (z - (s - u) / c)`. -/
theorem tateSubst_farEps {u c s : ℚ_[p]} (hu : ‖u‖ ≤ 1) (hc : ‖c‖ = 1) (hs : 1 < ‖s‖) :
    tateSubst u c (farEps s) = c⁻¹ • farEps ((s - u) / c) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have hs' : ‖s⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hs
  set t := s⁻¹ with ht
  have htu : ‖t * u‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans_lt hs'
  have hsu : s - u ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hs
    exact (hu.trans_lt hs).false
  have htu1 : 1 - t * u ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at htu
    exact lt_irrefl _ htu
  ext m
  refine HasSum.unique
    (hasSum_coeff_tateSubst (farEps_mem_tateAlgebra hs') hu hc.le m) ?_
  rw [← hasSum_nat_add_iff' m]
  have hzero : ∑ i ∈ Finset.range m,
      coeff i (farEps s) * coeff m ((C u + C c * X) ^ i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [coeff_add_mul_X_pow, show ¬m ≤ i by simpa using hi, ↓reduceIte, mul_zero]
  rw [hzero, sub_zero]
  convert (hasSum_choose_mul_geometric_of_norm_lt_one m htu).mul_left
    (-t ^ (m + 1) * c ^ m) using 1
  · ext n
    simp only [coeff_farEps, coeff_add_mul_X_pow, add_comm n m, ← ht,
      Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
    ring
  · have : ((s - u) / c)⁻¹ = c * t / (1 - t * u) := by
      rw [ht]
      field_simp
    rw [coeff_smul, coeff_farEps, this, div_pow, smul_eq_mul]
    field_simp
    ring

/-- For `s ∈ ℚ_p` with `|s|_p > 1`, the substitution `z ↦ z + 1` carries `ε_s` to `ε_{s-1}`. -/
theorem tateSubst_one_one_farEps {s : ℚ_[p]} (hs : 1 < ‖s‖) :
    tateSubst 1 1 (farEps s) = farEps (s - 1) := by
  simpa using tateSubst_farEps (u := (1 : ℚ_[p])) (c := 1) (by simp) (by simp) hs

/-- **Shifting `ε_s`.** For `s ∈ ℚ_p` with `v_p(s) < 0`, `ε_s(z + 1) = ε_{s-1}`. -/
@[zeta5irr "lem_tau_far_shift"]
theorem tateSubst_one_one_farEps_of_valuation_neg {s : ℚ_[p]} (hs : s.valuation < 0) :
    tateSubst 1 1 (farEps s) = farEps (s - 1) :=
  tateSubst_one_one_farEps (one_lt_norm_of_valuation_neg hs)

end Zeta5Irr
