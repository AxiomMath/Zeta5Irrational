/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.MomentFunctional

/-!
# The truncated moment functional `μ₀`

For a prime `p`, the truncated moment functional `μ₀ : ℚ[t] → ℚ_p` is the `ℚ`-linear map
determined on the monomial basis by
`μ₀(t ^ e) = μ(t ^ e)` for `0 ≤ e < 2p - 3` and `μ₀(t ^ e) = 0` for `e ≥ 2p - 3`,
where `μ` is the moment functional `Zeta5Irr.momentFunctional`, whose rational values are
viewed in `ℚ_p`. It is the integral part of `μ` in the outer range; the correction
`μ - μ₀` is supported on the monomials of degree at least `2p - 3`.

## Main definitions

* `Zeta5Irr.truncatedMomentFunctional`: the functional `μ₀`.

## Main results

* `Zeta5Irr.truncatedMomentFunctional_X_pow`: the defining values of `μ₀` on `t ^ e`.
* `Zeta5Irr.truncatedMomentFunctional_X_pow_of_lt`,
  `Zeta5Irr.truncatedMomentFunctional_X_pow_of_le`: the two cases separately.
* `Zeta5Irr.truncatedMomentFunctional_monomial`: the value on `c t ^ e`.
* `Zeta5Irr.truncatedMomentFunctional_apply`: `μ₀(f) = ∑_{e < 2p - 3} f_e μ(t ^ e)`.
* `Zeta5Irr.eq_truncatedMomentFunctional`: `μ₀` is the only linear map with these values.

## Implementation notes

* `μ₀` is built as `Polynomial.lsum` of the maps `c ↦ c μ(t ^ e)` (for `e < 2p - 3`) and `0`
  (otherwise), so that it is linear by construction.
* The bound `2p - 3` is a natural subtraction; it agrees with the source for every prime
  `p ≥ 2`, since `2p ≥ 4 > 3`.
* The primality of `p` is needed only for `ℚ_p` to be a field, hence a `ℚ`-vector space.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The truncated moment functional `μ₀ : ℚ[t] → ℚ_p`, the `ℚ`-linear map with
`μ₀(t ^ e) = μ(t ^ e)` for `e < 2p - 3` and `μ₀(t ^ e) = 0` for `e ≥ 2p - 3`. -/
@[zeta5irr "def_out_mu0"]
noncomputable def truncatedMomentFunctional : ℚ[X] →ₗ[ℚ] ℚ_[p] :=
  lsum fun e ↦ if e < 2 * p - 3 then
    LinearMap.toSpanSingleton ℚ ℚ_[p] (momentFunctional (X ^ e) : ℚ_[p]) else 0

variable {p}

/-- The value of the truncated moment functional on a monomial: `μ₀(c t ^ e) = c μ(t ^ e)` if
`e < 2p - 3` and `0` otherwise. -/
@[simp]
theorem truncatedMomentFunctional_monomial (e : ℕ) (c : ℚ) :
    truncatedMomentFunctional p (monomial e c) =
      if e < 2 * p - 3 then (c : ℚ_[p]) * momentFunctional (X ^ e) else 0 := by
  simp only [truncatedMomentFunctional, lsum_apply]
  split_ifs with h <;> simp [h, Rat.smul_def]

/-- The defining property of the truncated moment functional:
`μ₀(t ^ e) = μ(t ^ e)` if `e < 2p - 3` and `0` otherwise. -/
@[zeta5irr "def_out_mu0"]
theorem truncatedMomentFunctional_X_pow (e : ℕ) :
    truncatedMomentFunctional p (X ^ e) =
      if e < 2 * p - 3 then (momentFunctional (X ^ e) : ℚ_[p]) else 0 := by
  rw [← monomial_one_right_eq_X_pow, truncatedMomentFunctional_monomial]
  simp [monomial_one_right_eq_X_pow]

/-- `μ₀(t ^ e) = μ(t ^ e)` for `e < 2p - 3`. -/
theorem truncatedMomentFunctional_X_pow_of_lt {e : ℕ} (he : e < 2 * p - 3) :
    truncatedMomentFunctional p (X ^ e) = (momentFunctional (X ^ e) : ℚ_[p]) := by
  simp [truncatedMomentFunctional_X_pow, he]

/-- `μ₀(t ^ e) = 0` for `e ≥ 2p - 3`. -/
theorem truncatedMomentFunctional_X_pow_of_le {e : ℕ} (he : 2 * p - 3 ≤ e) :
    truncatedMomentFunctional p (X ^ e) = 0 := by
  simp [truncatedMomentFunctional_X_pow, he.not_gt]

/-- `μ₀(c t ^ e) = c μ(t ^ e)` if `e < 2p - 3` and `0` otherwise, for `c ∈ ℚ`. -/
theorem truncatedMomentFunctional_C_mul_X_pow (c : ℚ) (e : ℕ) :
    truncatedMomentFunctional p (C c * X ^ e) =
      if e < 2 * p - 3 then (c : ℚ_[p]) * momentFunctional (X ^ e) else 0 := by
  rw [C_mul_X_pow_eq_monomial, truncatedMomentFunctional_monomial]

/-- The value of the truncated moment functional on a polynomial:
`μ₀(f) = ∑ f_e μ(t ^ e)`, the sum over the exponents `e < 2p - 3` in the support of `f`. -/
theorem truncatedMomentFunctional_apply (f : ℚ[X]) :
    truncatedMomentFunctional p f =
      ∑ e ∈ f.support with e < 2 * p - 3, (f.coeff e : ℚ_[p]) * momentFunctional (X ^ e) := by
  conv_lhs => rw [f.as_sum_support]
  rw [map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [← C_mul_X_pow_eq_monomial, truncatedMomentFunctional_C_mul_X_pow]

/-- The truncated moment functional is the unique `ℚ`-linear map `ℚ[t] → ℚ_p` sending `t ^ e`
to `μ(t ^ e)` for `e < 2p - 3` and to `0` for `e ≥ 2p - 3`. -/
theorem eq_truncatedMomentFunctional {g : ℚ[X] →ₗ[ℚ] ℚ_[p]}
    (hg : ∀ e, g (X ^ e) = if e < 2 * p - 3 then (momentFunctional (X ^ e) : ℚ_[p]) else 0) :
    g = truncatedMomentFunctional p :=
  Polynomial.lhom_ext' fun e ↦ LinearMap.ext_ring <| by
    simpa [monomial_one_right_eq_X_pow, truncatedMomentFunctional_X_pow] using hg e

end Zeta5Irr
