/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.ScalingFactor
public import Zeta5Irr.Parameters.GramDeterminant

/-!
# The normalized determinant `F_K`

The polynomial `F_K(X) ∈ ℚ[X]` is the determinant `Δ_K(X) = det G_K(X)` rescaled by the
positive rational number `S_K`, that is `F_K(X) = S_K Δ_K(X)`. Since `S_K ≠ 0`, the
polynomial `F_K` has the same degree as `Δ_K`, and its leading coefficient is `S_K` times
that of `Δ_K`.

## Main definitions

* `Zeta5Irr.normalizedDet`: the polynomial `F_K(X) = S_K Δ_K(X)`.

## Main results

* `Zeta5Irr.eval_normalizedDet`: `F_K(x) = S_K Δ_K(x)` for every `x ∈ ℚ`.
* `Zeta5Irr.natDegree_normalizedDet`, `Zeta5Irr.degree_normalizedDet`: `F_K` and `Δ_K` have
  the same degree.
* `Zeta5Irr.leadingCoeff_normalizedDet`: the leading coefficient of `F_K` is `S_K` times
  that of `Δ_K`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The polynomial `F_K(X) = S_K Δ_K(X) ∈ ℚ[X]`, where `K = 40 n`. -/
@[zeta5irr "def_FK"]
noncomputable def normalizedDet (n : ℕ) : ℚ[X] :=
  C (scalingFactor n) * gramDet n

/-- `F_K` as a scalar multiple: `F_K = S_K • Δ_K`. -/
theorem normalizedDet_eq_smul (n : ℕ) : normalizedDet n = scalingFactor n • gramDet n :=
  (smul_eq_C_mul _).symm

/-- `F_K(x) = S_K Δ_K(x)`. -/
@[simp]
theorem eval_normalizedDet (n : ℕ) (x : ℚ) :
    (normalizedDet n).eval x = scalingFactor n * (gramDet n).eval x := by
  simp [normalizedDet]

/-- `F_K` and `Δ_K` have the same natural degree. -/
@[simp]
theorem natDegree_normalizedDet (n : ℕ) : (normalizedDet n).natDegree = (gramDet n).natDegree :=
  natDegree_C_mul (scalingFactor_ne_zero n)

/-- `F_K` and `Δ_K` have the same degree. -/
@[simp]
theorem degree_normalizedDet (n : ℕ) : (normalizedDet n).degree = (gramDet n).degree :=
  degree_C_mul (scalingFactor_ne_zero n)

/-- The leading coefficient of `F_K` is `S_K` times that of `Δ_K`. -/
@[simp]
theorem leadingCoeff_normalizedDet (n : ℕ) :
    (normalizedDet n).leadingCoeff = scalingFactor n * (gramDet n).leadingCoeff := by
  simp [normalizedDet]

/-- `F_K = 0` if and only if `Δ_K = 0`. -/
@[simp]
theorem normalizedDet_eq_zero_iff (n : ℕ) : normalizedDet n = 0 ↔ gramDet n = 0 := by
  simp [normalizedDet, scalingFactor_ne_zero]

end Zeta5Irr
