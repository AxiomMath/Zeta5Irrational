/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDist
public import Zeta5Irr.LocalFunctional.TauAnPoly
public import Zeta5Irr.LocalFunctional.TauLDist
public import Zeta5Irr.LocalFunctional.Tau

/-!
# The distributed functional without poles

Let `p` be a prime and `P ∈ ℚ[x]`. With no poles, `R = ∅`, the distributed functional
`𝒯_p(P; ∅) = p^{-4} ∑_{a=0}^{p-1} τ_{Y_p}^ext(δ_∅^ext(P(a + pz)))` reduces to the functional `τ`:
`𝒯_p(P; ∅) = τ(P)`. Indeed `E_∅ = 1`, so `δ_∅(U) = (U, ())` and `τ_Y^ext(U, ()) = τ^an(U)`,
which is `τ(U)` on rational polynomials. By the chain rule
`(P(a + px))''' = p^3 P'''(a + px)`, so `τ(P(a + px)) = p^3 L(P'''(a + px)) / 24`, and the
distribution relation `∑_a L(Q(a + px)) = p L(Q)` for `Q = P'''` gives
`∑_a τ(P(a + px)) = p^4 τ(P)`.

## Main results

* `Zeta5Irr.tauExt_deltaExt_empty_coe`: `τ_Y^ext(δ_∅^ext(U)) = τ^an(U)` for `U ∈ ℚ_p[z]`.
* `Zeta5Irr.sum_tau_comp`: `∑_{a<m} τ(P(a + mx)) = m^4 τ(P)` for `m ≠ 0`.
* `Zeta5Irr.tauDist_empty_eq_tau`: `𝒯_p(P; ∅) = τ(P)`.

## Implementation notes

* The source assumes `p ≥ 5`; the identity holds for every prime `p`, and is stated so.
* The value `τ(P) ∈ ℚ` is regarded in `ℚ_p[X]` as a constant polynomial.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- With no poles, `τ_Y^ext(δ_∅^ext(U)) = τ^an(U)` for every polynomial `U ∈ ℚ_p[z]`. -/
theorem tauExt_deltaExt_empty_coe {p : ℕ} [Fact p.Prime] (Y : ℚ_[p][X]) (U : ℚ_[p][X]) :
    tauExt ∅ Y (deltaExt ∅ (U : PowerSeries ℚ_[p])) = C (tauAn (U : PowerSeries ℚ_[p])) := by
  rw [deltaExt_coe, tauExt]
  simp [deltaR, intPoleProduct_empty]

/-- The distribution relation for `τ`: for `m ≠ 0` (in particular every prime) and
`P ∈ ℚ[x]`, `∑_{a<m} τ(P(a + mx)) = m^4 τ(P)`. -/
theorem sum_tau_comp {m : ℕ} (hm : m ≠ 0) (P : ℚ[X]) :
    ∑ a ∈ Finset.range m, tau (P.comp (C (a : ℚ) + C (m : ℚ) * X)) = (m : ℚ) ^ 4 * tau P := by
  simp only [tau_apply]
  simp only [iterate_derivative_comp_C_add_C_mul_X]
  have hC (c : ℚ) (Q : ℚ[X]) : bernoulliFunctional (C c * Q) = c * bernoulliFunctional Q := by
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  simp only [hC]
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_bernoulliFunctional_comp hm]
  ring

/-- **`𝒯_p(P; ∅) = τ(P)`.** For every prime `p` and `P ∈ ℚ[x]`, the distributed functional
without poles is the functional `τ`, regarded as a constant polynomial in `ℚ_p[X]`. -/
@[zeta5irr "lem_tau_dist_poly"]
theorem tauDist_empty_eq_tau {p : ℕ} [Fact p.Prime] (P : ℚ[X]) :
    tauDist p ∅ P = C ((tau P : ℚ) : ℚ_[p]) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [tauDist_empty, tauExt_deltaExt_empty_coe, tauAn_map_eq_tau, ← map_sum,
    ← Rat.cast_sum, sum_tau_comp (Fact.out : p.Prime).ne_zero, smul_C, smul_eq_mul]
  push_cast
  rw [inv_mul_cancel_left₀ (pow_ne_zero 4 hp)]
end Zeta5Irr
