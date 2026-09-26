/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.QKM
public import Zeta5Irr.RealDeterminant.RealPos

/-!
# `Q_{K,M}(ξ)` is positive

Let `ξ = ζ(5)`, let `M ≥ 40` and let `K` be a positive multiple of `40` with `K ≥ 200 M²`.
The normalized polynomial is `Q_{K,M}(X) = m_{K,M} F_K(X)` with `F_K(X) = S_K Δ_K(X)` and
`Δ_K(X) = det G_K(X)`. The matrix `G_K(ξ)` is positive definite, so `Δ_K(ξ) > 0`; the scaling
factor `S_K` is a quotient of products of positive integers and the normalizing factor
`m_{K,M}` is a finite product of positive numbers. Hence `Q_{K,M}(ξ) > 0`.

## Main results

* `Zeta5Irr.eval_normalizedPoly_zetaFive_pos`: `0 < Q_{K,M}(ξ)`.

## Implementation notes

As elsewhere, `K = 40 n` and the polynomial is indexed by `n` and `M`. None of the three
positivity facts uses the hypotheses `M ≥ 40`, `n ≥ 1` or `K ≥ 200 M²`, so the result is
stated for all `n` and `M`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- **`Q_{K,M}(ξ)` is positive.** For `ξ = ζ(5)` and `K = 40 n`, `0 < Q_{K,M}(ξ)`. -/
@[zeta5irr "lem_final_pos_K"]
theorem eval_normalizedPoly_zetaFive_pos (n M : ℕ) : 0 < (normalizedPoly n M).eval zetaFive := by
  rw [eval_normalizedPoly]
  exact mul_pos normalizingFactor_pos (aeval_normalizedDet_pos n)

end Zeta5Irr
