/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.RealPos
public import Zeta5Irr.RealDeterminant.RealSK
public import Zeta5Irr.RealDeterminant.RealDeltaK
public import Zeta5Irr.Measure.UBound

/-!
# The upper bound for `log F_K(ξ)`

Let `ξ = ζ(5)`, `K = 40 n`, `N = 3 n`, `h = 37 n`, and let `U = -2733991/2000000` be the
energy margin. Then
`log F_K(ξ) ≤ U K² + 24 K log K + 200 K`.

Since `F_K(ξ) = S_K Δ_K(ξ)` with both factors positive, `log F_K(ξ) = log S_K + log Δ_K(ξ)`,
and the statement follows by adding the bounds for `log S_K` and `log Δ_K(ξ)`. The two
coefficients of `K² log K`, namely `2 h (h + 6N - K) = (111/160) K²` and
`2λ - 12αλ - 2λ² = -111/160`, cancel; the coefficient of `K²` is
`λ M₀ - I(ρ) + C_* ≤ U`; and `24 h log K ≤ 24 K log K`, `166 h ≤ 200 K` since `h ≤ K`.

## Main results

* `Zeta5Irr.log_aeval_normalizedDet_le`: `log F_K(ξ) ≤ U K² + 24 K log K + 200 K`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3 (The Gram integral and scaling).
-/

@[expose] public section

open Real Polynomial

namespace Zeta5Irr

/-- **The upper bound for `log F_K(ξ)`.** With `ξ = ζ(5)`, `K = 40 n` and `U` the energy
margin, `log F_K(ξ) ≤ U K² + 24 K log K + 200 K`. -/
@[zeta5irr "prop_real"]
theorem log_aeval_normalizedDet_le {n : ℕ} (hn : 0 < n) :
    log (aeval zetaFive (normalizedDet n)) ≤
      energyMargin * (poleBound n : ℝ) ^ 2 + 24 * poleBound n * log (poleBound n) +
        200 * poleBound n := by
  rw [aeval_normalizedDet, log_mul (by exact_mod_cast (scalingFactor_pos n).ne')
    (aeval_gramDet_pos n).ne']
  have hS := log_scalingFactor_le (n := n) hn
  have hΔ := log_aeval_gramDet_le hn
  have hU := orderRatio_mul_potentialBound_sub_logEnergy_rho_add_normConstant_le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ log (poleBound n : ℝ) :=
    log_nonneg (by simp only [poleBound]; push_cast; linarith)
  simp only [poleBound, innerDegree, matrixOrder, orderRatio, innerRatio, potentialBound]
    at hS hΔ hU hL ⊢
  push_cast at hS hΔ hU hL ⊢
  set L := log (40 * (n : ℝ))
  set I := logEnergy (rho.map ((↑) : ℝ → ℂ))
  have hK2 : 0 ≤ (40 * (n : ℝ)) ^ 2 := by positivity
  have hq := mul_le_mul_of_nonneg_right hU hK2
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hL]

end Zeta5Irr
