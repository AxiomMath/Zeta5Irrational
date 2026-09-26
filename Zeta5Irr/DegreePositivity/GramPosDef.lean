/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.GramMatrix
public import Zeta5Irr.DegreePositivity.MuIntegral

/-!
# `G_K(ξ)` is positive definite

Let `ξ = ζ(5)`. By the positive integral representation, each entry of `G_K(ξ)` is
`G_K(ξ)_{ij} = ∫_0^∞ D_N(y²)^6 y^{2(i+j)} / D_K(y²) w(y) dy`. For `c ∈ ℝ^h` the quadratic
form is therefore
`∑_{i,j} c_i c_j G_K(ξ)_{ij} = ∫_0^∞ D_N(y²)^6 / D_K(y²) (∑_i c_i y^{2i})² w(y) dy`.
The integrand is nonnegative on `(0, ∞)`, and if `c ≠ 0` it vanishes only at the finitely
many positive roots of the nonzero polynomial `∑_i c_i Y^{2i}`; hence the integral is
positive.

## Main results

* `Zeta5Irr.sum_mul_aeval_gramMatrix_pos`: `∑_{i,j} c_i c_j G_K(ξ)_{ij} > 0` for `c ≠ 0`.
* `Zeta5Irr.posDef_map_aeval_gramMatrix`: `G_K(ξ)` is positive definite.

## Implementation notes

The source argues that the integrand is continuous and positive at some point, hence
positive on an interval. We instead observe that it is positive off a finite set, which has
measure zero, so that its support meets `(0, ∞)` in a set of infinite measure. No
hypothesis on `n` is needed: for `n = 0` there is no nonzero `c`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace Zeta5Irr

/-- The polynomial `∑_i c_i Y^{2i}` attached to a nonzero coefficient vector is nonzero. -/
theorem sum_C_mul_X_pow_two_mul_ne_zero {h : ℕ} {c : Fin h → ℝ} (hc : c ≠ 0) :
    ∑ i, C (c i) * X ^ (2 * (i : ℕ)) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  intro H
  have := congrArg (coeff · (2 * (i : ℕ))) H
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [show 2 * (i : ℕ) ≠ 2 * j from
    fun h => hj (Fin.ext (by omega)).symm]) (by simp)] at this
  exact hi (by simpa using this)

/-- **`G_K(ξ)` is positive definite.** For every nonzero `c ∈ ℝ^h`,
`∑_{0 ≤ i, j < h} c_i c_j G_K(ξ)_{ij} > 0`. -/
@[zeta5irr "prop_GK_posdef"]
theorem sum_mul_aeval_gramMatrix_pos (n : ℕ) {c : Fin (matrixOrder n) → ℝ} (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * aeval zetaFive (gramMatrix n i j) := by
  set S := Finset.Icc 1 (poleBound n)
  have hS : 0 ∉ S := by simp [S]
  set DN := poleProductRange (innerDegree n) ℚ
  set f : Fin (matrixOrder n) → Fin (matrixOrder n) → ℝ → ℝ := fun i j y =>
    aeval (y ^ 2) (DN ^ 6 * X ^ ((i : ℕ) + j)) / aeval (y ^ 2) (poleProduct S ℚ) * weight y
  have hf : ∀ i j, IntegrableOn (f i j) (Ioi 0) := fun i j =>
    integrableOn_aeval_div_aeval_poleProduct_mul_weight hS _
  set q : ℝ[X] := ∑ i, C (c i) * X ^ (2 * (i : ℕ))
  set g : ℝ → ℝ := fun y =>
    aeval (y ^ 2) DN ^ 6 / aeval (y ^ 2) (poleProduct S ℚ) * q.eval y ^ 2 * weight y
  have hfg : (fun y => ∑ i, ∑ j, c i * c j * f i j y) = g := by
    funext y
    simp only [f, g, q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_mul,
      map_pow, aeval_X, sq (Finset.sum _ _), Finset.mul_sum,
      Finset.sum_mul, pow_mul, pow_add]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : IntegrableOn g (Ioi 0) := by
    rw [← hfg]
    exact integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hf i j).const_mul _
  have hpos : ∀ y : ℝ, 0 < y → ∀ T : Finset ℕ, 0 < aeval (y ^ 2) (poleProduct T ℚ) :=
    fun y hy T => by
      rw [aeval_poleProduct]
      exact Finset.prod_pos fun j _ => by positivity
  have hsum : ∑ i, ∑ j, c i * c j * aeval zetaFive (gramMatrix n i j) = ∫ y in Ioi 0, g y := by
    rw [← hfg, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hf i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hf i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, gramMatrix_apply, aeval_rationalFunctional_eq_integral hS]
  rw [hsum, setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · -- the support of `g` in `(0, ∞)` contains the complement of a finite set
    have hZ : {y : ℝ | q.IsRoot y}.Finite :=
      Polynomial.finite_setOfPred_isRoot (sum_C_mul_X_pow_two_mul_ne_zero hc)
    have hsub : Ioi 0 \ {y : ℝ | q.IsRoot y} ⊆ Function.support g ∩ Ioi 0 := by
      rintro y ⟨hy, hq⟩
      refine ⟨?_, hy⟩
      have hy : (0 : ℝ) < y := hy
      have hDN : 0 < aeval (y ^ 2) DN := hpos y hy _
      have := hpos y hy S
      have := weight_pos hy
      have hq : q.eval y ≠ 0 := hq
      simp only [Function.mem_support, g]
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null (hZ.measure_zero volume), Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y (hy : 0 < y) => ?_
    have := hpos y hy S
    have := (weight_pos hy).le
    simp only [Pi.zero_apply, g]
    have : 0 ≤ aeval (y ^ 2) DN ^ 6 := Even.pow_nonneg (by decide) _
    positivity

/-- `G_K(ξ)` is a positive definite real matrix. -/
theorem posDef_map_aeval_gramMatrix (n : ℕ) : ((gramMatrix n).map (aeval zetaFive)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun c hc => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (gramMatrix_isSymm n).map _
  · convert sum_mul_aeval_gramMatrix_pos n hc using 1
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

end Zeta5Irr
