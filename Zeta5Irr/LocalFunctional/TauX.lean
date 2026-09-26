/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.ReflectIndex
public import Zeta5Irr.LocalFunctional.Tau
public import Mathlib.RingTheory.PiTensorProduct

/-!
# The functional `τ_X`

Let `R ⊆ ℤ` be finite and `A ∈ ℚ[x]`. Writing `A = P E_R + B` with `deg B < #R`, where
`E_R = ∏_{r ∈ R} (x - r)`, the functional `τ_X` is
`τ_X(A; R) = τ(P) + ∑_{r ∈ R} A(r) / E_R'(r) · (H_{d(r)}^{(5)} - X) ∈ ℚ[X]`,
a polynomial of degree at most one in the formal variable `X`. The quotient `P` is the
polynomial part of the rational function `A / E_R`, and the numbers `A(r) / E_R'(r)` are its
residues at the simple poles `r ∈ R`.

## Main definitions

* `Zeta5Irr.tauX`: the functional `τ_X(A; R) ∈ ℚ[X]`.

## Main results

* `Zeta5Irr.tauX_eq_of_eq_add`: `τ_X(A; R)` may be computed from any decomposition
  `A = P E_R + B` with `deg B < #R`.
* `Zeta5Irr.tauX_add`, `Zeta5Irr.tauX_smul`, `Zeta5Irr.tauX_zero`: `τ_X(·; R)` is `ℚ`-linear.

## Implementation notes

The quotient `P` is `A /ₘ E_R`, the division of `A` by the monic polynomial `E_R`; the
decomposition is unique, so this agrees with the source's `P` for every admissible choice of
`B` (`tauX_eq_of_eq_add`). The formal variable `X` of the target is the variable of `ℚ[X]`, the
same polynomial ring as the argument `A`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.1 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C derivative eval)

/-- The functional `τ_X(A; R) = τ(P) + ∑_{r ∈ R} A(r) / E_R'(r) · (H_{d(r)}^{(5)} - X)`, where
`P = A /ₘ E_R` is the quotient of `A` by the pole polynomial `E_R = ∏_{r ∈ R} (x - r)`. -/
@[zeta5irr "def_tauX"]
noncomputable def tauX (R : Finset ℤ) (A : ℚ[X]) : ℚ[X] :=
  C (tau (A /ₘ intPoleProduct R ℚ)) +
    ∑ r ∈ R, C (A.eval (r : ℚ) / (derivative (intPoleProduct R ℚ)).eval (r : ℚ)) *
      (C (harmonicFive (reflectIndex r)) - X)

/-- `τ_X(A; R)` computed from any decomposition `A = P E_R + B` with `deg B < #R`. -/
@[zeta5irr "def_tauX"]
theorem tauX_eq_of_eq_add {R : Finset ℤ} {A P B : ℚ[X]}
    (hA : A = P * intPoleProduct R ℚ + B) (hB : B.degree < R.card) :
    tauX R A = C (tau P) +
      ∑ r ∈ R, C (A.eval (r : ℚ) / (derivative (intPoleProduct R ℚ)).eval (r : ℚ)) *
        (C (harmonicFive (reflectIndex r)) - X) := by
  rw [tauX, divByMonic_intPoleProduct_eq_of_eq_mul_add R ℚ hA hB]

/-- `τ_X(·; R)` is additive. -/
@[zeta5irr "lem_tauX_add"]
theorem tauX_add (R : Finset ℤ) (A₁ A₂ : ℚ[X]) :
    tauX R (A₁ + A₂) = tauX R A₁ + tauX R A₂ := by
  simp only [tauX, Polynomial.add_divByMonic, map_add, Polynomial.eval_add, add_div,
    Finset.sum_add_distrib, add_mul]
  ring

/-- `τ_X(·; R)` is `ℚ`-homogeneous. -/
@[zeta5irr "lem_tauX_smul"]
theorem tauX_smul (R : Finset ℤ) (c : ℚ) (A : ℚ[X]) :
    tauX R (c • A) = c • tauX R A := by
  rw [tauX, tauX, Polynomial.smul_divByMonic, map_smul, smul_add, Finset.smul_sum]
  congr 1
  · rw [smul_eq_mul, map_mul, Polynomial.smul_eq_C_mul]
  · refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Polynomial.eval_smul, smul_eq_mul, mul_div_assoc, map_mul, Polynomial.smul_eq_C_mul,
      mul_assoc]

/-- `τ_X(0; R) = 0`. -/
@[simp]
theorem tauX_zero (R : Finset ℤ) : tauX R 0 = 0 := by
  simpa using tauX_smul R 0 0

end Zeta5Irr
