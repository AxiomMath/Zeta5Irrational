/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleValue
public import Zeta5Irr.LocalEstimates.OutMu0

/-!
# The integral part `μ_{0,X}` of the functional on rational functions

Let `p` be a prime, `S ⊆ ℤ_{>0}` finite and `A ∈ ℚ[t]`. Divide `A` by the monic pole product
`D_S(t) = ∏_{j ∈ S} (t + j ^ 2)`, writing `A = P D_S + B` with `deg B < deg D_S`, and set
`μ_{0,X}(A; S) = μ₀(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) · ν_j(X) ∈ ℚ_p[X]`,
where `μ₀` is the truncated moment functional and `ν_j(X)` the pole value. This is the
integral part, in the outer range, of the functional applied to the rational function
`A / D_S`: the polynomial part `P` is sent through `μ₀`, and the partial-fraction
coefficients `A(-j ^ 2) / D_S'(-j ^ 2)` of `B / D_S` weight the values `ν_j(X)` of the
functional on the simple poles `1 / (t + j ^ 2)`.

## Main definitions

* `Zeta5Irr.truncatedPoleFunctional`: the `ℚ`-linear map `A ↦ μ_{0,X}(A; S)`.

## Main results

* `Zeta5Irr.truncatedPoleFunctional_apply`: the defining formula, with `P = A /ₘ D_S`.
* `Zeta5Irr.truncatedPoleFunctional_eq_of_eq_add`: for any decomposition `A = P D_S + B` with
  `deg B < deg D_S`, `μ_{0,X}(A; S) = μ₀(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) · ν_j(X)`.

## Implementation notes

* The quotient `P` is Mathlib's `Polynomial.divByMonic`, `A /ₘ D_S`; since `D_S` is monic,
  the decomposition `A = P D_S + B` with `deg B < deg D_S` is unique, and
  `truncatedPoleFunctional_eq_of_eq_add` states the definition for an arbitrary such
  decomposition, as in the source.
* The value lies in `ℚ_p[X]`: `μ₀(P) ∈ ℚ_p` is a constant polynomial, and the pole values
  `ν_j(X) ∈ ℚ[X]` are mapped to `ℚ_p[X]` coefficientwise.
* The functional is bundled as a `ℚ`-linear map in `A`, since it is expanded over sums and
  scalar multiples of polynomials.
* The index set is a `Finset ℕ`; positivity of the indices is not needed for the definition.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ) [Fact p.Prime] (S : Finset ℕ)

/-- The integral part `μ_{0,X}(A; S) = μ₀(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) · ν_j(X)`
of the functional on `A / D_S`, where `P = A /ₘ D_S` is the quotient of `A` by the pole
product `D_S`, as a `ℚ`-linear map `ℚ[t] → ℚ_p[X]`. -/
@[zeta5irr "def_out_muX0"]
noncomputable def truncatedPoleFunctional : ℚ[X] →ₗ[ℚ] ℚ_[p][X] where
  toFun A := C (truncatedMomentFunctional p (A /ₘ poleProduct S ℚ)) +
    ∑ j ∈ S, (A.eval (-((j : ℚ) ^ 2)) / (derivative (poleProduct S ℚ)).eval (-((j : ℚ) ^ 2))) •
      (poleValue j).map (Rat.castHom ℚ_[p])
  map_add' A B := by
    simp only [add_divByMonic, map_add, eval_add, add_div, add_smul,
      Finset.sum_add_distrib]
    ring
  map_smul' c A := by
    simp only [smul_divByMonic, map_smul, eval_smul, smul_eq_mul, mul_div_assoc, mul_smul,
      RingHom.id_apply, smul_add, Finset.smul_sum]
    rw [smul_C]

variable {p S}

/-- The defining formula of `μ_{0,X}`:
`μ_{0,X}(A; S) = μ₀(A /ₘ D_S) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) · ν_j(X)`. -/
@[zeta5irr "def_out_muX0"]
theorem truncatedPoleFunctional_apply (A : ℚ[X]) :
    truncatedPoleFunctional p S A = C (truncatedMomentFunctional p (A /ₘ poleProduct S ℚ)) +
      ∑ j ∈ S, (A.eval (-((j : ℚ) ^ 2)) / (derivative (poleProduct S ℚ)).eval (-((j : ℚ) ^ 2))) •
        (poleValue j).map (Rat.castHom ℚ_[p]) :=
  rfl

/-- `μ_{0,X}` may be computed from any decomposition `A = P D_S + B` with `deg B < deg D_S`:
then `μ_{0,X}(A; S) = μ₀(P) + ∑_{j ∈ S} A(-j ^ 2) / D_S'(-j ^ 2) · ν_j(X)`. -/
theorem truncatedPoleFunctional_eq_of_eq_add {A P B : ℚ[X]} (hA : A = P * poleProduct S ℚ + B)
    (hB : B.degree < (poleProduct S ℚ).degree) :
    truncatedPoleFunctional p S A = C (truncatedMomentFunctional p P) +
      ∑ j ∈ S, (A.eval (-((j : ℚ) ^ 2)) / (derivative (poleProduct S ℚ)).eval (-((j : ℚ) ^ 2))) •
        (poleValue j).map (Rat.castHom ℚ_[p]) := by
  have hP : A /ₘ poleProduct S ℚ = P :=
    (div_modByMonic_unique P B (monic_poleProduct S ℚ)
      ⟨by rw [hA]; ring, hB⟩).1
  rw [truncatedPoleFunctional_apply, hP]

end Zeta5Irr
