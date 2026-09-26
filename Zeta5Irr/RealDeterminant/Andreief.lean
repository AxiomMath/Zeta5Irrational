/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.RealAndreiefGeneral
public import Zeta5Irr.RealDeterminant.RealEntryIntegral
public import Zeta5Irr.RealDeterminant.RealGramIntegrable
public import Zeta5Irr.RealDeterminant.RealDetPos

/-!
# `Δ_K(ξ)` as an `h`-fold integral

Let `ξ = ζ(5)`, `K = 40 n`, `N = 3 n` and `h = 37 n`. The determinant `Δ_K(ξ)` of the Gram
matrix `G_K(ξ)` is the `h`-fold integral
`Δ_K(ξ) = (1 / h!) ∫_{(0,∞)^h} ∏_{i<j} (y_i² - y_j²)² ∏_i D_N(y_i²)⁶ / D_K(y_i²) w(y_i) dy`.

Indeed, by the integral formula for the entries,
`G_K(ξ)_{ij} = ∫_0^∞ y^{2i} y^{2j} dm(y)` for the measure `dm(y) = D_N(y²)⁶ / D_K(y²) w(y) dy`
on `(0, ∞)`, so the Andréief identity applied to `f_i(y) = g_i(y) = y^{2i}` expresses
`Δ_K(ξ) = det G_K(ξ)` as `1 / h!` times the integral of the square of the Vandermonde
determinant `det [y_k^{2i}] = ∏_{k<l} (y_l² - y_k²)`.

## Main results

* `Zeta5Irr.aeval_gramDet_eq_integral`: the `h`-fold integral formula for `Δ_K(ξ)`.

## Implementation notes

The measure `m` is not introduced as a measure with density: the density
`D_N(y²)⁶ / D_K(y²) w(y)` is absorbed into the functions `f_i(y) = y^{2i} D_N(y²)⁶ / D_K(y²) w(y)`
while `g_j(y) = y^{2j}` and the base measure is Lebesgue measure restricted to `(0, ∞)`. The
density then factors out of `det [f_i(y_k)]` column by column. The domain `(0, ∞)^h` is the
box `Set.univ.pi fun _ => Set.Ioi 0` in `Fin h → ℝ` with its Lebesgue measure.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (the Gram integral and scaling).
-/

@[expose] public section

open MeasureTheory Set Polynomial Matrix

namespace Zeta5Irr

/-- **Andréief expansion of `Δ_K(ξ)`.** With `ξ = ζ(5)`, `K = 40 n`, `N = 3 n`, `h = 37 n`,
`Δ_K(ξ) = (1 / h!) ∫_{(0,∞)^h} ∏_{i<j} (y_i² - y_j²)² ∏_i D_N(y_i²)⁶ / D_K(y_i²) w(y_i) dy`. -/
@[zeta5irr "lem_andreief"]
theorem aeval_gramDet_eq_integral (n : ℕ) :
    aeval zetaFive (gramDet n) =
      ((matrixOrder n).factorial : ℝ)⁻¹ *
        ∫ y in univ.pi fun _ : Fin (matrixOrder n) => Ioi (0 : ℝ),
          (∏ i, ∏ j ∈ Finset.Ioi i, (y i ^ 2 - y j ^ 2) ^ 2) *
            ∏ i, (poleProductRange (innerDegree n) ℝ).eval (y i ^ 2) ^ 6 /
              (poleProductRange (poleBound n) ℝ).eval (y i ^ 2) * weight (y i) := by
  set d : ℝ → ℝ := fun y => (poleProductRange (innerDegree n) ℝ).eval (y ^ 2) ^ 6 /
    (poleProductRange (poleBound n) ℝ).eval (y ^ 2) * weight y
  let f : Fin (matrixOrder n) → ℝ → ℝ := fun i y => y ^ (2 * (i : ℕ)) * d y
  let g : Fin (matrixOrder n) → ℝ → ℝ := fun j y => y ^ (2 * (j : ℕ))
  have hfg : ∀ i j, Integrable (fun y => f i y * g j y) (volume.restrict (Ioi 0)) := by
    intro i j
    refine (integrableOn_gramIntegrand ((i : ℕ) + j) (innerDegree n) (poleBound n)).congr_fun
      (fun y _ => ?_) measurableSet_Ioi
    simp only [f, g, d]
    ring
  have key := det_integral_mul_eq (volume.restrict (Ioi (0 : ℝ))) f g hfg
  rw [Fintype.card_fin] at key
  rw [aeval_gramDet]
  have hG : (gramMatrix n).map (aeval zetaFive) =
      Matrix.of fun i j => ∫ y in Ioi 0, f i y * g j y := by
    ext i j
    rw [map_apply, aeval_gramMatrix_eq_integral]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [f, g, d]
    ring
  rw [hG, key, ← Measure.restrict_pi_pi, ← volume_pi]
  congr 1
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioi) fun y _ => ?_
  have hV : (Matrix.of fun j l : Fin (matrixOrder n) => g j (y l)).det =
      ∏ i, ∏ j ∈ Finset.Ioi i, (y j ^ 2 - y i ^ 2) := by
    rw [← det_vandermonde, ← det_transpose]
    congr 1
    ext i j
    simp [g, vandermonde, pow_mul]
  have hF : (Matrix.of fun i k : Fin (matrixOrder n) => f i (y k)).det =
      (∏ k, d (y k)) * (Matrix.of fun j l : Fin (matrixOrder n) => g j (y l)).det := by
    rw [← det_mul_row]
    congr 1
    ext i k
    simp only [f, g, of_apply]
    ring
  rw [hF, hV, mul_assoc, mul_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

end Zeta5Irr
