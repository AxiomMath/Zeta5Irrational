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
# The entries of `G_K(ξ)` as integrals

Let `ξ = ζ(5)`, `K = 40 n`, `N = 3 n` and `h = 37 n`. For `0 ≤ i, j < h` the entry of the
Gram matrix `G_K(X)` evaluated at `X = ξ` is the integral
`G_K(ξ)_{ij} = ∫_0^∞ y^{2(i+j)} D_N(y²)⁶ / D_K(y²) w(y) dy`
against the weight `w`. This is the positive integral representation of `μ_ξ(A; S)` applied
to `A(t) = D_N(t)⁶ t^{i+j}` and `S = {1, …, K}`, whose pole product is `D_K`.

## Main results

* `Zeta5Irr.aeval_gramMatrix_eq_integral`:
  `G_K(ξ)_{ij} = ∫_0^∞ y^{2(i+j)} D_N(y²)⁶ / D_K(y²) w(y) dy`.

## Implementation notes

The source proves the formula by dividing `A = P D_K + B` and integrating the two parts
separately; this division is already carried out, for arbitrary `A`, in the positive integral
representation `Zeta5Irr.aeval_rationalFunctional_eq_integral`, so here it only remains to
identify the integrand. The polynomials `D_N`, `D_K` are evaluated over `ℝ`, as in
`Zeta5Irr.integrableOn_gramIntegrand`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (the Gram integral and scaling).
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace Zeta5Irr

/-- **The entries of `G_K(ξ)` as integrals.** For `0 ≤ i, j < h`,
`G_K(ξ)_{ij} = ∫_0^∞ y^{2(i+j)} D_N(y²)⁶ / D_K(y²) w(y) dy`. -/
@[zeta5irr "lem_real_entry_integral"]
theorem aeval_gramMatrix_eq_integral (n : ℕ) (i j : Fin (matrixOrder n)) :
    aeval zetaFive (gramMatrix n i j) =
      ∫ y in Ioi 0, y ^ (2 * ((i : ℕ) + j)) *
        (poleProductRange (innerDegree n) ℝ).eval (y ^ 2) ^ 6 /
          (poleProductRange (poleBound n) ℝ).eval (y ^ 2) * weight y := by
  rw [gramMatrix_apply, aeval_rationalFunctional_eq_integral (by simp)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  have hD (m : ℕ) :
      aeval (y ^ 2) (poleProduct (Finset.Icc 1 m) ℚ) = (poleProductRange m ℝ).eval (y ^ 2) := by
    rw [aeval_def, eval₂_eq_eval_map, ← poleProductRange, map_poleProductRange]
  simp only [map_mul, map_pow, aeval_X, poleProductRange, hD, pow_mul, pow_add]
  ring

end Zeta5Irr
