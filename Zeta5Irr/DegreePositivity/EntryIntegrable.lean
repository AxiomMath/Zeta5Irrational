/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.WeightIntegrable

/-!
# Integrability of the entries against the weight

Let `S` be a finite set of positive integers and `A` a polynomial. On the real line the pole
product satisfies `D_S(y²) = ∏_{j ∈ S} (y² + j²) ≥ ∏_{j ∈ S} j² > 0`, so the function
`y ↦ A(y²) / D_S(y²) · w(y)` is continuous on `(0, ∞)` and bounded in absolute value by
`(∏_{j ∈ S} j²)⁻¹ ∑_e |a_e| y^{2e} w(y)`, a finite nonnegative combination of the integrable
polynomial moments of the weight. Hence it is integrable on `(0, ∞)`.

## Main results

* `Zeta5Irr.integrableOn_aeval_div_aeval_poleProduct_mul_weight`: the function
  `y ↦ A(y²) / D_S(y²) · w(y)` is integrable on `(0, ∞)`.

## Implementation notes

The set `S ⊂ ℤ_{>0}` is a `Finset ℕ` with `0 ∉ S`; nonemptiness is not needed. The polynomial
`A` has coefficients in any commutative semiring `R` with an `R`-algebra structure on `ℝ`, which
covers `A ∈ ℚ[t]`; both `A` and `D_S` are evaluated at `y²` through `Polynomial.aeval`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the positive integral representation).
-/

@[expose] public section

open MeasureTheory Polynomial Finset

namespace Zeta5Irr

/-- **The entries are integrable against the weight.** For a finite set `S` of positive
integers and a polynomial `A`, the function `y ↦ A(y²) / D_S(y²) · w(y)` is integrable on
`(0, ∞)`. -/
@[zeta5irr "lem_w_entry_integrable"]
theorem integrableOn_aeval_div_aeval_poleProduct_mul_weight {R : Type*} [CommSemiring R]
    [Algebra R ℝ] {S : Finset ℕ} (hS : 0 ∉ S) (A : R[X]) :
    IntegrableOn (fun y : ℝ => aeval (y ^ 2) A / aeval (y ^ 2) (poleProduct S R) * weight y)
      (Set.Ioi 0) := by
  set B : ℝ[X] := A.map (algebraMap R ℝ)
  set c : ℝ := ∏ j ∈ S, ((j : ℝ) ^ 2)
  have hA : ∀ y : ℝ, aeval y A = B.eval y := fun y => by
    simp [B, aeval_def, eval_map]
  have hc : 0 < c := prod_pos fun j hj => by
    have : j ≠ 0 := fun h => hS (h ▸ hj)
    positivity
  have hD : ∀ y : ℝ, c ≤ ∏ j ∈ S, (y ^ 2 + (j : ℝ) ^ 2) := fun y =>
    Finset.prod_le_prod₀ (fun _ _ => by positivity) fun _ _ => by nlinarith [sq_nonneg y]
  simp only [hA, aeval_poleProduct]
  have hg : IntegrableOn (fun y : ℝ => c⁻¹ *
      ∑ i ∈ range (B.natDegree + 1), |B.coeff i| * (y ^ (2 * i) * weight y)) (Set.Ioi 0) :=
    (integrable_finsetSum _ fun i _ =>
      (integrableOn_pow_mul_weight (2 * i)).const_mul _).const_mul _
  refine hg.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun y (hy : 0 < y) => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun y _ =>
      (hc.trans_le (hD y)).ne') continuousOn_weight
  · have hw := (weight_pos hy).le
    have hDy := hc.trans_le (hD y)
    rw [norm_mul, norm_div, Real.norm_of_nonneg hw, Real.norm_of_nonneg hDy.le, Real.norm_eq_abs]
    have hB : |B.eval (y ^ 2)| ≤ ∑ i ∈ range (B.natDegree + 1), |B.coeff i| * y ^ (2 * i) := by
      rw [eval_eq_sum_range]
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y ^ 2) ^ i), ← pow_mul]
    calc |B.eval (y ^ 2)| / (∏ j ∈ S, (y ^ 2 + (j : ℝ) ^ 2)) * weight y
        ≤ |B.eval (y ^ 2)| / c * weight y := by gcongr; exact hD y
      _ ≤ (∑ i ∈ range (B.natDegree + 1), |B.coeff i| * y ^ (2 * i)) / c * weight y := by
        gcongr
      _ = _ := by rw [div_eq_inv_mul, mul_assoc, sum_mul]; simp only [mul_assoc]

end Zeta5Irr
