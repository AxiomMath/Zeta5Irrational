/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MuX
public import Zeta5Irr.DegreePositivity.WeightPole
public import Zeta5Irr.DegreePositivity.WeightMoment
public import Zeta5Irr.DegreePositivity.EntryIntegrable
public import Zeta5Irr.DegreePositivity.PartialFractions

/-!
# The positive integral representation

Let `S` be a finite set of positive integers and `A ∈ ℚ[t]`. The value of the rational
functional `μ_X(A; S)` at `X = ξ = ζ(5)` is the integral
`∫_0^∞ A(y²) / D_S(y²) w(y) dy` against the weight `w`.

Divide `A = P D_S + B` with `deg B < #S`. Then `A(y²) / D_S(y²) = P(y²) + B(y²) / D_S(y²)`,
and the second term splits into simple fractions
`∑_{j ∈ S} B(-j²) / D_S'(-j²) · 1 / (y² + j²)`, where `B(-j²) = A(-j²)` since `D_S(-j²) = 0`.
Integrating term by term, the polynomial part gives `μ(P)` by the moment identity
`∫_0^∞ y^{2e} w(y) dy = m(e)`, and each pole gives `ν_j(ξ)`.

## Main results

* `Zeta5Irr.integral_aeval_sq_mul_weight`: `∫_0^∞ P(y²) w(y) dy = μ(P)` for `P ∈ ℚ[t]`.
* `Zeta5Irr.aeval_rationalFunctional_eq_integral`: `μ_X(A; S)` at `X = ξ` equals
  `∫_0^∞ A(y²) / D_S(y²) w(y) dy`.

## Implementation notes

The source takes `S` finite and nonempty. Nonemptiness is not needed: for `S = ∅` the pole
product is `1` and both sides are `μ(A)`. Positivity is expressed as `0 ∉ S` for
`S : Finset ℕ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace Zeta5Irr

/-- The moment functional as an integral: `∫_0^∞ P(y²) w(y) dy = μ(P)` for `P ∈ ℚ[t]`. -/
theorem integral_aeval_sq_mul_weight (P : ℚ[X]) :
    ∫ y in Ioi 0, aeval (y ^ 2) P * weight y = (momentFunctional P : ℝ) := by
  have hint : ∀ Q : ℚ[X], IntegrableOn (fun y : ℝ => aeval (y ^ 2) Q * weight y) (Ioi 0) :=
    fun Q => by
      simpa [poleProduct_empty] using
        integrableOn_aeval_div_aeval_poleProduct_mul_weight (S := ∅) (Finset.notMem_empty 0) Q
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul, Rat.cast_add]
    rw [integral_add (hint p) (hint q), hp, hq]
  | monomial e c =>
    simp only [aeval_monomial, momentFunctional_monomial, Rat.cast_mul, eq_ratCast, ← pow_mul,
      mul_assoc]
    rw [integral_const_mul, integral_Ioi_pow_mul_weight]

/-- **The positive integral representation.** For a finite `S ⊆ ℤ_{>0}` and `A ∈ ℚ[t]`, the
value of `μ_X(A; S)` at `X = ξ` is `∫_0^∞ A(y²) / D_S(y²) w(y) dy`. -/
@[zeta5irr "prop_mu_integral"]
theorem aeval_rationalFunctional_eq_integral {S : Finset ℕ} (hS : 0 ∉ S) (A : ℚ[X]) :
    aeval zetaFive (rationalFunctional S A) =
      ∫ y in Ioi 0, aeval (y ^ 2) A / aeval (y ^ 2) (poleProduct S ℚ) * weight y := by
  set D := poleProduct S ℚ with hD
  set P := A /ₘ D
  set B := A %ₘ D
  set c : ℕ → ℚ := fun j => A.eval (-(j : ℚ) ^ 2) / (derivative D).eval (-(j : ℚ) ^ 2)
  have hAPB : A = P * D + B := by
    rw [mul_comm, add_comm]; exact (modByMonic_add_div A D).symm
  have hB : B.degree < S.card := by
    rw [← degree_poleProduct S ℚ]
    exact degree_modByMonic_lt A (monic_poleProduct S ℚ)
  have hBA : ∀ j ∈ S, B.eval (-(j : ℚ) ^ 2) = A.eval (-(j : ℚ) ^ 2) := fun j hj => by
    conv_rhs => rw [hAPB]
    rw [eval_add, eval_mul, eval_neg_sq_poleProduct_of_mem hj, mul_zero, zero_add]
  have hDpos : ∀ y : ℝ, aeval (y ^ 2) D ≠ 0 := fun y => by
    rw [hD, aeval_poleProduct]
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have : j ≠ 0 := fun h => hS (h ▸ hj)
    positivity
  -- the pointwise decomposition of the integrand
  have hpt : ∀ y : ℝ, aeval (y ^ 2) A / aeval (y ^ 2) D * weight y =
      aeval (y ^ 2) P * weight y + ∑ j ∈ S, (c j : ℝ) * (weight y / (y ^ 2 + (j : ℝ) ^ 2)) := by
    intro y
    have h1 : aeval (y ^ 2) A / aeval (y ^ 2) D =
        aeval (y ^ 2) P + aeval (y ^ 2) B / aeval (y ^ 2) D := by
      conv_lhs => rw [hAPB]
      rw [map_add, map_mul, add_div, mul_div_cancel_right₀ _ (hDpos y)]
    rw [h1, aeval_sq_div_poleProduct_eq_sum hS hB y, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hBA j hj]
    ring
  have hpole : ∀ j ∈ S, IntegrableOn
      (fun y : ℝ => (c j : ℝ) * (weight y / (y ^ 2 + (j : ℝ) ^ 2))) (Ioi 0) := fun j hj => by
    have h := integrableOn_aeval_div_aeval_poleProduct_mul_weight (S := {j})
      (by simpa using fun h : 0 = j => hS (h ▸ hj)) (1 : ℚ[X])
    refine IntegrableOn.congr_fun (h.const_mul (c j : ℝ)) (fun y _ => ?_) measurableSet_Ioi
    simp [aeval_poleProduct, div_eq_mul_inv, mul_comm]
  have hPint : IntegrableOn (fun y : ℝ => aeval (y ^ 2) P * weight y) (Ioi 0) := by
    simpa [poleProduct_empty] using
      integrableOn_aeval_div_aeval_poleProduct_mul_weight (S := ∅) (Finset.notMem_empty 0) P
  simp_rw [hpt]
  rw [integral_add hPint (integrable_finsetSum _ hpole), integral_finsetSum _ hpole,
    integral_aeval_sq_mul_weight, rationalFunctional_apply]
  simp only [map_add, map_sum, map_mul, aeval_C, eq_ratCast]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 := fun h => hS (h ▸ hj)
  rw [integral_const_mul, integral_weight_div_sq_add_natCast_sq hj0]

end Zeta5Irr
