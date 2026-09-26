/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.MKM
public import Zeta5Irr.Parameters.NormalizedDeterminant

/-!
# The normalized polynomial `Q_{K,M}`

For an integer `M ≥ 40` and an integer `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, the normalized
polynomial is
```
Q_{K,M}(X) = m_{K,M} F_K(X),
```
the normalized determinant `F_K` rescaled by the normalizing factor `m_{K,M}`. The factor
`m_{K,M}` is positive, so `Q_{K,M}` has the same degree as `F_K`, and its value at any real
point is `m_{K,M}` times that of `F_K`.

## Main definitions

* `Zeta5Irr.normalizedPoly`: the polynomial `Q_{K,M}(X) = m_{K,M} F_K(X)`.

## Main results

* `Zeta5Irr.coeff_normalizedPoly`: the coefficients of `Q_{K,M}` are `m_{K,M}` times those
  of `F_K`.
* `Zeta5Irr.eval_normalizedPoly`: `Q_{K,M}(x) = m_{K,M} F_K(x)` for every real `x`.
* `Zeta5Irr.natDegree_normalizedPoly`, `Zeta5Irr.degree_normalizedPoly`: `Q_{K,M}` and `F_K`
  have the same degree.
* `Zeta5Irr.normalizedPoly_eq_map`: when `m_{K,M}` is a rational number `q`, the polynomial
  `Q_{K,M}` is the image in `ℝ[X]` of the rational polynomial `q F_K`.

## Implementation notes

* As for `m_{K,M}` and `F_K`, the polynomial is indexed by `n`, `M`, with `K = 40 n`. The
  source's hypotheses on `K` and `M` are not needed to write the product down, so the
  definition is total.
* The normalizing factor `m_{K,M}` is defined as a real number: that the local exponents
  `L_p(K, M)` are integers, so that `m_{K,M}` is rational, is a separate result. Accordingly
  `Q_{K,M}` is a polynomial with real coefficients, the product of the constant `m_{K,M}` with
  the image of `F_K ∈ ℚ[X]` in `ℝ[X]`. The statement that `Q_{K,M}` has integer coefficients
  is then that every coefficient lies in the image of `ℤ → ℝ`, and evaluation at the real
  number `ζ(5)` is `Polynomial.eval`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1 (The normalizing factor and integrality).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The normalized polynomial `Q_{K,M}(X) = m_{K,M} F_K(X) ∈ ℝ[X]`, where `K = 40 n`. -/
@[zeta5irr "def_QKM"]
noncomputable def normalizedPoly (n M : ℕ) : ℝ[X] :=
  C (normalizingFactor n M) * (normalizedDet n).map (algebraMap ℚ ℝ)

variable {n M : ℕ}

/-- `Q_{K,M}` as a scalar multiple: `Q_{K,M} = m_{K,M} • F_K`. -/
theorem normalizedPoly_eq_smul :
    normalizedPoly n M = normalizingFactor n M • (normalizedDet n).map (algebraMap ℚ ℝ) :=
  (smul_eq_C_mul _).symm

/-- The coefficients of `Q_{K,M}` are `m_{K,M}` times those of `F_K`. -/
@[simp]
theorem coeff_normalizedPoly (i : ℕ) :
    (normalizedPoly n M).coeff i = normalizingFactor n M * ((normalizedDet n).coeff i : ℝ) := by
  simp [normalizedPoly]

/-- `Q_{K,M}(x) = m_{K,M} F_K(x)` for every real `x`. -/
@[simp]
theorem eval_normalizedPoly (x : ℝ) :
    (normalizedPoly n M).eval x = normalizingFactor n M * aeval x (normalizedDet n) := by
  simp [normalizedPoly, eval_map_algebraMap]

/-- `Q_{K,M}` and `F_K` have the same natural degree. -/
@[simp]
theorem natDegree_normalizedPoly :
    (normalizedPoly n M).natDegree = (normalizedDet n).natDegree := by
  rw [normalizedPoly, natDegree_C_mul normalizingFactor_pos.ne', natDegree_map]

/-- `Q_{K,M}` and `F_K` have the same degree. -/
@[simp]
theorem degree_normalizedPoly : (normalizedPoly n M).degree = (normalizedDet n).degree := by
  rw [normalizedPoly, degree_C_mul normalizingFactor_pos.ne', degree_map]

/-- `Q_{K,M} = 0` if and only if `F_K = 0`. -/
@[simp]
theorem normalizedPoly_eq_zero_iff : normalizedPoly n M = 0 ↔ normalizedDet n = 0 := by
  simp [normalizedPoly, normalizingFactor_pos.ne', Polynomial.map_eq_zero_iff
    (algebraMap ℚ ℝ).injective]

/-- If the normalizing factor `m_{K,M}` is the rational number `q`, then `Q_{K,M}` is the image
in `ℝ[X]` of the rational polynomial `q F_K`. -/
theorem normalizedPoly_eq_map {q : ℚ} (hq : normalizingFactor n M = q) :
    normalizedPoly n M = (C q * normalizedDet n).map (algebraMap ℚ ℝ) := by
  rw [normalizedPoly, hq, Polynomial.map_mul, map_C]
  rfl

end Zeta5Irr
