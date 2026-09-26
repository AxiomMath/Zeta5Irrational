/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs

/-!
# The moment functional

The moment functional `μ : ℚ[t] → ℚ` is the `ℚ`-linear map determined by its
values `μ(t ^ e) = m(e)` on the monomial basis, where `m(e)` is the Bernoulli
moment `Zeta5Irr.bernoulliMoment`. Explicitly, `μ(∑ₑ cₑ t ^ e) = ∑ₑ cₑ m(e)`.

## Main definitions

* `Zeta5Irr.momentFunctional`: the functional `μ`.

## Main results

* `Zeta5Irr.momentFunctional_X_pow`: `μ(t ^ e) = m(e)`.
* `Zeta5Irr.momentFunctional_monomial`, `Zeta5Irr.momentFunctional_C`,
  `Zeta5Irr.momentFunctional_X`: the values on `c t ^ e`, on constants and on `t`.
* `Zeta5Irr.momentFunctional_apply`: `μ(p) = ∑ₑ pₑ m(e)`, the sum over the support.
* `Zeta5Irr.eq_momentFunctional`: `μ` is the only linear map with `μ(t ^ e) = m(e)`
  for all `e`.

## Implementation notes

* `μ` is built as `Polynomial.lsum` of the maps `c ↦ c * m(e)`, so that it is
  linear by construction; its value on a polynomial is recovered by
  `Zeta5Irr.momentFunctional_apply`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and
  the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The moment functional `μ : ℚ[t] → ℚ`, the `ℚ`-linear map with `μ(t ^ e) = m(e)`
for every `e`, where `m` is the Bernoulli moment. -/
@[zeta5irr "def_mu"]
noncomputable def momentFunctional : ℚ[X] →ₗ[ℚ] ℚ :=
  lsum fun e ↦ LinearMap.mulRight ℚ (bernoulliMoment e)

/-- The value of the moment functional on a polynomial: `μ(p) = ∑ₑ pₑ m(e)`. -/
theorem momentFunctional_apply (p : ℚ[X]) :
    momentFunctional p = ∑ e ∈ p.support, p.coeff e * bernoulliMoment e := by
  simp [momentFunctional, lsum_apply, Polynomial.sum_def]

/-- The value of the moment functional on a monomial: `μ(c t ^ e) = c m(e)`. -/
@[simp]
theorem momentFunctional_monomial (e : ℕ) (c : ℚ) :
    momentFunctional (monomial e c) = c * bernoulliMoment e := by
  simp [momentFunctional, lsum_apply]

/-- The defining property of the moment functional: `μ(t ^ e) = m(e)`. -/
@[simp, zeta5irr "def_mu"]
theorem momentFunctional_X_pow (e : ℕ) : momentFunctional (X ^ e) = bernoulliMoment e := by
  rw [← monomial_one_right_eq_X_pow, momentFunctional_monomial, one_mul]

/-- The value of the moment functional on a constant: `μ(c) = c m(0)`. -/
@[simp]
theorem momentFunctional_C (c : ℚ) : momentFunctional (C c) = c * bernoulliMoment 0 := by
  rw [← monomial_zero_left, momentFunctional_monomial]

/-- The value of the moment functional on `1`: `μ(1) = m(0)`. -/
@[simp]
theorem momentFunctional_one : momentFunctional 1 = bernoulliMoment 0 := by
  simpa using momentFunctional_X_pow 0

/-- The value of the moment functional on `t`: `μ(t) = m(1)`. -/
@[simp]
theorem momentFunctional_X : momentFunctional X = bernoulliMoment 1 := by
  simpa using momentFunctional_X_pow 1

/-- The value of the moment functional on `c t ^ e`: `μ(c t ^ e) = c m(e)`. -/
theorem momentFunctional_C_mul_X_pow (c : ℚ) (e : ℕ) :
    momentFunctional (C c * X ^ e) = c * bernoulliMoment e := by
  rw [C_mul_X_pow_eq_monomial, momentFunctional_monomial]

/-- The moment functional is the unique `ℚ`-linear map `ℚ[t] → ℚ` sending `t ^ e`
to `m(e)` for every `e`. -/
theorem eq_momentFunctional {f : ℚ[X] →ₗ[ℚ] ℚ} (hf : ∀ e, f (X ^ e) = bernoulliMoment e) :
    f = momentFunctional :=
  Polynomial.lhom_ext' fun e ↦ LinearMap.ext_ring <| by
    simpa [monomial_one_right_eq_X_pow] using hf e

end Zeta5Irr
