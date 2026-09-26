/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.EntryPoles
public import Zeta5Irr.LocalEstimates.OutLcorr
public import Zeta5Irr.LocalEstimates.OutMomentVal
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Integrality of the correction matrix of the outer range

Let `p ≥ 7` be a prime and fix the parameters `N = 3 n`, `K = 40 n` and `h = 37 n`. Every entry
of the correction matrix `𝓛_p = p (G_K - G_K^∘)` is a `p`-adic integer: `(𝓛_p)_{kl} ∈ ℤ_p` for
`0 ≤ k, l < h`.

Put `A = D_N ^ 5 t ^ (k + l)`, `S = {N + 1, …, K}` and write `A = P_{kl} D_S + B` with
`deg B < deg D_S`. The residue parts of `(G_K)_{kl} = μ_X(A; S)` and of
`(G_K^∘)_{kl} = μ_{0,X}(A; S)` coincide, so
`(𝓛_p)_{kl} = p (μ(P_{kl}) - μ₀(P_{kl})) = p ∑_{e ≥ 2p - 3} [t ^ e] P_{kl} · μ(t ^ e)`.
Since `A ∈ ℤ[t]` and `D_S` is monic over `ℤ`, `P_{kl} ∈ ℤ[t]`; and `v_p(μ(t ^ e)) ≥ -1`, so
each summand, hence the sum, lies in `ℤ_p`.

## Main results

* `Zeta5Irr.exists_outerCorrectionMatrix_apply_eq_C_padicInt`: `(𝓛_p)_{kl}` is the constant
  polynomial with value a `p`-adic integer.
* `Zeta5Irr.outerCorrectionMatrix_apply_eq_C`: `(𝓛_p)_{kl} = p (μ(P_{kl}) - μ₀(P_{kl}))`.
* `Zeta5Irr.momentFunctional_sub_truncatedMomentFunctional`:
  `μ(f) - μ₀(f) = ∑_{e ≥ 2p - 3} [t ^ e] f · μ(t ^ e)`.

## Implementation notes

* The entries of `𝓛_p` live in `ℚ_p[X]`; the statement `(𝓛_p)_{kl} ∈ ℤ_p` is formalized as
  `(𝓛_p)_{kl} = C z` for some `z : ℤ_[p]`, which records in addition that the entry is a
  constant polynomial (the residue parts cancel).
* The hypothesis `p ≥ 7` of the source is weakened to `p ≥ 5`, which is all that the valuation
  bound `v_p(μ(t ^ e)) ≥ -1` needs; the hypothesis `n > 0` is not needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- `μ(f) - μ₀(f) = ∑_{e ≥ 2p - 3} [t ^ e] f · μ(t ^ e)`: the two functionals agree on the
monomials of degree `< 2p - 3`. -/
theorem momentFunctional_sub_truncatedMomentFunctional (f : ℚ[X]) :
    (momentFunctional f : ℚ_[p]) - truncatedMomentFunctional p f =
      ∑ e ∈ f.support with 2 * p - 3 ≤ e, (f.coeff e : ℚ_[p]) * momentFunctional (X ^ e) := by
  rw [momentFunctional_apply, truncatedMomentFunctional_apply, Rat.cast_sum,
    ← sum_filter_add_sum_filter_not f.support (fun e ↦ e < 2 * p - 3)]
  simp only [not_lt, Rat.cast_mul, momentFunctional_X_pow, add_sub_cancel_left]

/-- The residue parts of `μ_X(A; S)` and `μ_{0,X}(A; S)` agree, so their difference is the
constant `μ(P) - μ₀(P)` with `P = A /ₘ D_S`. -/
theorem map_rationalFunctional_sub_truncatedPoleFunctional (S : Finset ℕ) (A : ℚ[X]) :
    (rationalFunctional S A).map (algebraMap ℚ ℚ_[p]) - truncatedPoleFunctional p S A =
      C ((momentFunctional (A /ₘ poleProduct S ℚ) : ℚ_[p]) -
        truncatedMomentFunctional p (A /ₘ poleProduct S ℚ)) := by
  rw [rationalFunctional_apply, truncatedPoleFunctional_apply, Polynomial.map_add,
    Polynomial.map_sum, C_sub]
  simp only [Polynomial.map_mul, map_C, Algebra.smul_def, Polynomial.algebraMap_apply,
    eq_ratCast]
  have : (Rat.castHom ℚ_[p]) = algebraMap ℚ ℚ_[p] := by ext; simp
  rw [this]
  ring

/-- `(𝓛_p)_{kl} = p (μ(P_{kl}) - μ₀(P_{kl}))`, where `P_{kl} = D_N ^ 5 t ^ (k + l) /ₘ D_S` and
`S = {N + 1, …, K}`. -/
theorem outerCorrectionMatrix_apply_eq_C (n : ℕ) (k l : Fin (matrixOrder n)) :
    outerCorrectionMatrix p n k l =
      C ((p : ℚ_[p]) *
        ((momentFunctional (poleProductRange (innerDegree n) ℚ ^ 5 * X ^ ((k : ℕ) + l) /ₘ
            poleProduct (Icc (innerDegree n + 1) (poleBound n)) ℚ) : ℚ_[p]) -
          truncatedMomentFunctional p (poleProductRange (innerDegree n) ℚ ^ 5 *
            X ^ ((k : ℕ) + l) /ₘ poleProduct (Icc (innerDegree n + 1) (poleBound n)) ℚ))) := by
  rw [outerCorrectionMatrix_apply, gramMatrix_apply_eq, outerIntegralGramMatrix_apply,
    outerIntegralForm, mul_assoc, ← pow_add, map_rationalFunctional_sub_truncatedPoleFunctional,
    smul_C, smul_eq_mul]

/-- For `p ≥ 5`, `‖p μ(t ^ e)‖_p ≤ 1`. -/
theorem norm_natCast_mul_momentFunctional_X_pow_le_one (hp : 5 ≤ p) (e : ℕ) :
    ‖(p : ℚ_[p]) * momentFunctional (X ^ e)‖ ≤ 1 := by
  have hq := neg_one_le_padicValRat_momentFunctional_X_pow hp e
  set q := momentFunctional (X ^ e)
  rw [show (p : ℚ_[p]) * q = ((p * q : ℚ) : ℚ_[p]) by push_cast; rfl, Padic.eq_padicNorm]
  by_cases hq0 : q = 0
  · simp [hq0]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [padicNorm.eq_zpow_of_nonzero (mul_ne_zero hp0 hq0), padicValRat.mul hp0 hq0,
    padicValRat.self (Fact.out : p.Prime).one_lt]
  push_cast
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) (by omega)

/-- For `p ≥ 5` and `f ∈ ℤ[t]`, `‖p (μ(f) - μ₀(f))‖_p ≤ 1`. -/
theorem norm_natCast_mul_momentFunctional_sub_truncated_le_one (hp : 5 ≤ p) (f : ℤ[X]) :
    ‖(p : ℚ_[p]) * ((momentFunctional (f.map (Int.castRingHom ℚ)) : ℚ_[p]) -
      truncatedMomentFunctional p (f.map (Int.castRingHom ℚ)))‖ ≤ 1 := by
  rw [momentFunctional_sub_truncatedMomentFunctional, mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ ↦ ?_
  rw [coeff_map, eq_intCast, Rat.cast_intCast, mul_left_comm, norm_mul]
  simpa using mul_le_mul (Padic.norm_int_le_one _)
    (norm_natCast_mul_momentFunctional_X_pow_le_one hp e) (norm_nonneg _) zero_le_one

/-- **Integrality of the correction matrix.** For a prime `p ≥ 5` (in the source, `p ≥ 7`)
and `0 ≤ k, l < h`, the entry `(𝓛_p)_{kl}` is a constant `p`-adic integer. -/
@[zeta5irr "lem_out_L_int"]
theorem exists_outerCorrectionMatrix_apply_eq_C_padicInt (hp : 5 ≤ p) (n : ℕ)
    (k l : Fin (matrixOrder n)) :
    ∃ z : ℤ_[p], outerCorrectionMatrix p n k l = C (z : ℚ_[p]) := by
  set S := Icc (innerDegree n + 1) (poleBound n)
  have hP : poleProductRange (innerDegree n) ℚ ^ 5 * X ^ ((k : ℕ) + l) /ₘ poleProduct S ℚ =
      (poleProductRange (innerDegree n) ℤ ^ 5 * X ^ ((k : ℕ) + l) /ₘ poleProduct S ℤ).map
        (Int.castRingHom ℚ) := by
    rw [map_divByMonic _ (monic_poleProduct S ℤ), Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, map_X, map_poleProductRange, map_poleProduct]
  rw [outerCorrectionMatrix_apply_eq_C, hP]
  exact ⟨⟨_, norm_natCast_mul_momentFunctional_sub_truncated_le_one hp _⟩, rfl⟩

end Zeta5Irr
