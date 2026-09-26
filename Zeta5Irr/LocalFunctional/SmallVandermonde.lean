/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom

/-!
# Vandermonde's identity for the binomial polynomials

For every `k ≥ 0`, in `ℚ[x, w]`,
`(x + w choose k) = ∑_{j=0}^{k} (x choose j) (w choose (k - j))`.

We prove the identity after evaluating the binomial polynomials at arbitrary elements `x`, `w`
of an arbitrary commutative `ℚ`-algebra `A`. Taking `A = ℚ[x, w]` (as `MvPolynomial (Fin 2) ℚ`)
and `x`, `w` the two variables gives the polynomial identity; taking `A` a field such as `ℚ_p`
gives the identity of values.

## Main results

* `Zeta5Irr.aeval_add_qbinom`: for `x, w` in a commutative `ℚ`-algebra,
  `(x + w choose k) = ∑_{j=0}^{k} (x choose j) (w choose (k - j))`.
* `Zeta5Irr.aeval_X_add_X_qbinom`: the same identity in `ℚ[x, w]`.
* `Zeta5Irr.descPochhammer_smeval_eq_factorial_mul_aeval_qbinom`: the falling factorial
  `a (a - 1) ⋯ (a - k + 1)` equals `k! (a choose k)`.

## Implementation notes

The source proves the polynomial identity by checking it at all pairs of natural numbers,
where it is the Vandermonde convolution `Nat.add_choose_eq`, and then using that a polynomial
in two variables vanishing on `ℕ × ℕ` is zero. We instead multiply through by `k!` and use the
Chu–Vandermonde identity for falling factorials, `Ring.descPochhammer_smeval_add`, which holds
in any ring; this gives the more general statement in any commutative `ℚ`-algebra directly.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Nat Finset

/-- In a commutative `ℚ`-algebra, the falling factorial `a (a - 1) ⋯ (a - k + 1)` equals
`k! (a choose k)`. -/
theorem descPochhammer_smeval_eq_factorial_mul_aeval_qbinom {A : Type*} [CommRing A]
    [Algebra ℚ A] (k : ℕ) (a : A) :
    (descPochhammer ℤ k).smeval a = (k ! : A) * aeval a (qbinom k) := by
  rw [← map_natCast (algebraMap ℚ A), ← Algebra.smul_def, ← map_smul, factorial_smul_qbinom,
    ← descPochhammer_map (Int.castRingHom ℚ), ← algebraMap_int_eq, aeval_map_algebraMap,
    aeval_eq_smeval]

/-- **Vandermonde's identity** for the binomial polynomials, evaluated in a commutative
`ℚ`-algebra: `(x + w choose k) = ∑_{j=0}^{k} (x choose j) (w choose (k - j))`. -/
@[zeta5irr "lem_small_vandermonde"]
theorem aeval_add_qbinom {A : Type*} [CommRing A] [Algebra ℚ A] (k : ℕ) (x w : A) :
    aeval (x + w) (qbinom k) =
      ∑ j ∈ range (k + 1), aeval x (qbinom j) * aeval w (qbinom (k - j)) := by
  have hk : IsUnit (k ! : A) := by
    rw [← map_natCast (algebraMap ℚ A)]
    exact (IsUnit.mk0 _ (by positivity)).map _
  refine hk.mul_left_cancel ?_
  rw [← descPochhammer_smeval_eq_factorial_mul_aeval_qbinom,
    Ring.descPochhammer_smeval_add k (Commute.all x w),
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simp only [descPochhammer_smeval_eq_factorial_mul_aeval_qbinom]
  rw [← Nat.choose_mul_factorial_mul_factorial hjk]
  push_cast
  ring

/-- **Vandermonde's identity** for the binomial polynomials in `ℚ[x, w]`, with `x = X 0` and
`w = X 1`: `(x + w choose k) = ∑_{j=0}^{k} (x choose j) (w choose (k - j))`. -/
@[zeta5irr "lem_small_vandermonde"]
theorem aeval_X_add_X_qbinom (k : ℕ) :
    aeval (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) (qbinom k) =
      ∑ j ∈ range (k + 1),
        aeval (MvPolynomial.X 0) (qbinom j) * aeval (MvPolynomial.X 1) (qbinom (k - j)) :=
  aeval_add_qbinom k _ _

end Zeta5Irr
