/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MomentFunctional
public import Zeta5Irr.Parameters.PoleValue
public import Mathlib.RingTheory.PiTensorProduct

/-!
# The rational functional

Let `S` be a finite set of positive integers and `A ∈ ℚ[t]`. Dividing `A` by the monic pole
product `D_S`, write `A = P D_S + B` with `deg B < deg D_S`, and set
`μ_X(A; S) = μ(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X) ∈ ℚ[X]`,
where `μ` is the moment functional and `ν_j(X)` the pole value. This is the value of the
functional of the construction on the rational function `A / D_S`: the quotient `P` carries
the polynomial part, and `A(-j ^ 2) / D_S'(-j ^ 2)` is the coefficient of `1 / (t + j ^ 2)`
in the partial-fraction expansion of `A / D_S`.

## Main definitions

* `Zeta5Irr.rationalFunctional`: for fixed `S`, the `ℚ`-linear map `A ↦ μ_X(A; S)`.

## Main results

* `Zeta5Irr.rationalFunctional_apply`: `μ_X(A; S)` computed with the quotient `A /ₘ D_S`.
* `Zeta5Irr.rationalFunctional_eq_of_eq_mul_add`: for *any* `P`, `B` with `A = P D_S + B`
  and `deg B < deg D_S`, `μ_X(A; S) = μ(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X)`;
  so the value does not depend on how the division is carried out.
* `Zeta5Irr.rationalFunctional_of_degree_lt`: if `deg A < deg D_S` then `μ(P)` vanishes.
* `Zeta5Irr.rationalFunctional_empty`: `μ_X(A; ∅)` is the constant `μ(A)`.

## Implementation notes

* Two indeterminates appear, both modelled by `ℚ[X]`: the argument `A` is a polynomial in
  the variable `t` of the source, and the value `μ_X(A; S)` is a polynomial in the variable
  `X` of the source (later specialised to `ξ = ζ(5)`). The number `μ(P) ∈ ℚ` enters the
  value as the constant polynomial `C (μ(P))`.
* Since `D_S` is monic, the division `A = P D_S + B` is realised by `P = A /ₘ D_S` and
  `B = A %ₘ D_S`. With this choice the map is additive and homogeneous in `A`, and it is
  packaged as a `ℚ`-linear map `ℚ[t] →ₗ[ℚ] ℚ[X]` for each `S`.
* The source takes `S ⊂ ℤ_{>0}`; here `S : Finset ℕ` with no positivity hypothesis, which
  the definition does not need.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The rational functional `μ_X(A; S) = μ(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X)`,
where `P = A /ₘ D_S` is the quotient of `A` by the pole product `D_S`; as a function of `A`
it is `ℚ`-linear. It is the value of the functional on the rational function `A / D_S`. -/
@[zeta5irr "def_muX"]
noncomputable def rationalFunctional (S : Finset ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun A := C (momentFunctional (A /ₘ poleProduct S ℚ)) +
    ∑ j ∈ S, C (A.eval (-(j : ℚ) ^ 2) / (derivative (poleProduct S ℚ)).eval (-(j : ℚ) ^ 2)) *
      poleValue j
  map_add' A₁ A₂ := by
    simp only [add_divByMonic, map_add, eval_add, add_div, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c A := by
    rw [RingHom.id_apply, smul_divByMonic, map_smul, smul_add, Finset.smul_sum]
    simp only [smul_eq_C_mul, smul_eq_mul, eval_mul, eval_C, mul_div_assoc, C_mul, mul_assoc]

/-- `μ_X(A; S)` computed with the quotient `P = A /ₘ D_S`. -/
theorem rationalFunctional_apply (S : Finset ℕ) (A : ℚ[X]) :
    rationalFunctional S A = C (momentFunctional (A /ₘ poleProduct S ℚ)) +
      ∑ j ∈ S, C (A.eval (-(j : ℚ) ^ 2) / (derivative (poleProduct S ℚ)).eval (-(j : ℚ) ^ 2)) *
        poleValue j :=
  rfl

/-- The defining formula of `μ_X(A; S)` for an arbitrary division `A = P D_S + B` with
`deg B < deg D_S`: `μ_X(A; S) = μ(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X)`. -/
@[zeta5irr "def_muX"]
theorem rationalFunctional_eq_of_eq_mul_add {S : Finset ℕ} {A P B : ℚ[X]}
    (hA : A = P * poleProduct S ℚ + B) (hB : B.degree < (poleProduct S ℚ).degree) :
    rationalFunctional S A = C (momentFunctional P) +
      ∑ j ∈ S, C (A.eval (-(j : ℚ) ^ 2) / (derivative (poleProduct S ℚ)).eval (-(j : ℚ) ^ 2)) *
        poleValue j := by
  have hP : A /ₘ poleProduct S ℚ = P :=
    (div_modByMonic_unique P B (monic_poleProduct S ℚ) ⟨by rw [hA]; ring, hB⟩).1
  rw [rationalFunctional_apply, hP]

/-- If `deg A < deg D_S` the polynomial part vanishes:
`μ_X(A; S) = ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) ν_j(X)`. -/
theorem rationalFunctional_of_degree_lt {S : Finset ℕ} {A : ℚ[X]}
    (hA : A.degree < (poleProduct S ℚ).degree) :
    rationalFunctional S A =
      ∑ j ∈ S, C (A.eval (-(j : ℚ) ^ 2) / (derivative (poleProduct S ℚ)).eval (-(j : ℚ) ^ 2)) *
        poleValue j := by
  rw [rationalFunctional_eq_of_eq_mul_add (P := 0) (B := A) (by ring) hA, map_zero, C_0,
    zero_add]

/-- With no poles, `μ_X(A; ∅)` is the constant polynomial `μ(A)`. -/
@[simp]
theorem rationalFunctional_empty (A : ℚ[X]) :
    rationalFunctional ∅ A = C (momentFunctional A) := by
  simp [rationalFunctional_apply]

end Zeta5Irr
