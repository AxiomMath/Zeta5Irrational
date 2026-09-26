/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.DegreePositivity.Weight
public import Zeta5Irr.DegreePositivity.EntryIntegrable

/-!
# Integrability of the Gram integrand

For integers `e, N, K ≥ 0`, the Gram integrand
`y ↦ y^{2e} D_N(y²)⁶ / D_K(y²) · w(y)` is integrable on `(0, ∞)`, so that
`∫_0^∞ y^{2e} D_N(y²)⁶ / D_K(y²) w(y) dy < ∞`. Indeed it is `A(y²) / D_K(y²) · w(y)` for the
polynomial `A(t) = t^e D_N(t)⁶`, and `D_K(y²) = ∏_{j=1}^{K} (y² + j²) ≥ 1` on the real line,
so it is dominated by a finite nonnegative combination of the polynomial moments
`y^k w(y)` of the weight, each of which is integrable since
`w(y) ≤ 8192 (1 + y)⁵ e^{-2πy}`.

## Main results

* `Zeta5Irr.integrableOn_gramIntegrand`: the function
  `y ↦ y^{2e} D_N(y²)⁶ / D_K(y²) · w(y)` is integrable on `(0, ∞)`.

## Implementation notes

The source's `∫ … < ∞` is rendered as `MeasureTheory.IntegrableOn` on `Set.Ioi 0`, which for
this nonnegative integrand is the same statement and is the form in which it is used. The
source has `N = 3n` and `K = 40n`; the statement holds for all `N, K : ℕ` and is stated so.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3: the Gram integral and scaling.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace Zeta5Irr

/-- **The Gram integrand is integrable.** For all `e, N, K : ℕ`, the function
`y ↦ y^{2e} D_N(y²)⁶ / D_K(y²) · w(y)` is integrable on `(0, ∞)`; in particular
`∫_0^∞ y^{2e} D_N(y²)⁶ / D_K(y²) w(y) dy < ∞`. -/
@[zeta5irr "lem_real_gram_integrable"]
theorem integrableOn_gramIntegrand (e N K : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * (poleProductRange N ℝ).eval (y ^ 2) ^ 6 /
      (poleProductRange K ℝ).eval (y ^ 2) * weight y) (Set.Ioi 0) := by
  have h := integrableOn_aeval_div_aeval_poleProduct_mul_weight (R := ℝ)
    (S := Finset.Icc 1 K) (by simp) (X ^ e * poleProductRange N ℝ ^ 6)
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [map_mul, map_pow, aeval_X, coe_aeval_eq_eval, poleProductRange, pow_mul]

end Zeta5Irr
