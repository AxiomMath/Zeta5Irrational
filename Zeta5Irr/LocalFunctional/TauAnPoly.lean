/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauAn
public import Zeta5Irr.LocalFunctional.TauMonomial
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# `τ^an` agrees with `τ` on rational polynomials

A polynomial `P ∈ ℚ[x]`, regarded as an element of the Tate algebra `𝒜 = ℚ_p⟨z⟩` via `x ↦ z`
and `ℚ ⊂ ℚ_p`, has finitely many nonzero coefficients, so the series defining `τ^an(P)` is the
finite sum `∑_d P_d κ_d`. Since `τ` is `ℚ`-linear and `τ(x^d) = κ_d`, this sum is also `τ(P)`.
Hence `τ^an(P) = τ(P)`.

## Main results

* `Zeta5Irr.tau_eq_sum_coeff_mul_kappa`: `τ(P) = ∑_d P_d κ_d` for `P ∈ ℚ[x]`.
* `Zeta5Irr.tauAn_map_eq_tau`: `τ^an(P) = τ(P)` for `P ∈ ℚ[x]`, viewed in `ℚ_p⟨z⟩`.

## Implementation notes

* The embedding `ℚ[x] → ℚ_p⟨z⟩` is written as `Polynomial.map (algebraMap ℚ ℚ_[p])` followed
  by the coercion `Polynomial ℚ_[p] → ℚ_[p]⟦X⟧`; that its image lies in `ℚ_p⟨z⟩` is
  `Zeta5Irr.coe_mem_tateAlgebra`. Since `Zeta5Irr.tauAn` is defined on all of `ℚ_[p]⟦X⟧`, no
  membership hypothesis is needed in the statement.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- `τ(P) = ∑_{d ∈ supp P} P_d κ_d` for every `P ∈ ℚ[x]`. -/
theorem tau_eq_sum_coeff_mul_kappa (P : ℚ[X]) :
    tau P = ∑ d ∈ P.support, P.coeff d * kappa d := by
  conv_lhs => rw [P.as_sum_support]
  simp [map_sum, ← Polynomial.smul_X_eq_monomial, tau_X_pow_eq_kappa]

/-- For every `P ∈ ℚ[x]`, regarded as an element of `ℚ_p⟨z⟩` by `x ↦ z` and `ℚ ⊂ ℚ_p`,
`τ^an(P) = τ(P)`. -/
@[zeta5irr "lem_tau_an_poly"]
theorem tauAn_map_eq_tau (P : ℚ[X]) :
    tauAn ((P.map (algebraMap ℚ ℚ_[p]) : ℚ_[p][X]) : ℚ_[p]⟦X⟧) = (tau P : ℚ_[p]) := by
  rw [tauAn_coe_polynomial, tau_eq_sum_coeff_mul_kappa,
    Polynomial.support_map_of_injective _ (algebraMap ℚ ℚ_[p]).injective]
  simp

end Zeta5Irr
