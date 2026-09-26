/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.BernoulliFunctional
public import Zeta5Irr.LocalFunctional.TauUmbral
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.ENatToNat

/-!
# The distribution relation for the Bernoulli functional

Let `L : ℚ[X] → ℚ` be the Bernoulli functional, `L (X ^ k) = B_k`. For every positive integer
`m` (in particular for every prime `p`) and every `Q : ℚ[X]`,
`∑_{a=0}^{m-1} L (Q (a + m x)) = m L(Q)`.

By linearity it suffices to treat `Q = X ^ n`. Then `(a + m x) ^ n = m ^ n (x + a / m) ^ n`, so the
umbral identity gives `L ((a + m x) ^ n) = m ^ n B_n(a / m)`, and the multiplication theorem for
the Bernoulli polynomials at `0`, `B_n(0) = m ^ (n - 1) ∑_{i<m} B_n(i / m)`, finishes the proof.

## Main results

* `Zeta5Irr.bernoulli_eval_distribution`: `m ^ n ∑_{i<m} B_n(i / m) = m B_n(0)` in `ℚ`.
* `Zeta5Irr.sum_bernoulliFunctional_comp`: `∑_{a<m} L (Q.comp (a + m X)) = m L(Q)` for `m ≠ 0`.

## Implementation notes

The source states the relation for a prime `p`; the proof only uses `p ≠ 0`, so we state it for
every nonzero natural number `m`. The multiplication theorem is available in Mathlib for the
real Bernoulli functions (`bernoulliFun_mul`); we transfer it to `ℚ` along the injective map
`ℚ → ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X C)

/-- The multiplication theorem for the rational Bernoulli polynomials at `0`:
`m ^ n ∑_{i<m} B_n(i / m) = m B_n(0)` for every `m ≠ 0`. -/
theorem bernoulli_eval_distribution (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (m : ℚ) ^ n * ∑ i ∈ Finset.range m, (Polynomial.bernoulli n).eval ((i : ℚ) / m) =
      m * (Polynomial.bernoulli n).eval 0 := by
  have h := bernoulliFun_mul n hm 0
  simp only [mul_zero, zero_add, bernoulliFun] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  apply (algebraMap ℚ ℝ).injective
  have key : ∀ x : ℚ, algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval x) =
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).eval (algebraMap ℚ ℝ x) := fun x =>
    (Polynomial.hom_eval₂ _ _ _ _).trans (by simp [Polynomial.eval_map])
  simp only [map_mul, map_pow, map_natCast, map_sum, key, map_div₀, map_zero] at *
  rw [h]
  field_simp

/-- The distribution relation for the Bernoulli functional: for every `m ≠ 0` (in particular
every prime) and every `Q : ℚ[X]`, `∑_{a<m} L (Q (a + m x)) = m L(Q)`. -/
@[zeta5irr "lem_tau_L_dist"]
theorem sum_bernoulliFunctional_comp {m : ℕ} (hm : m ≠ 0) (Q : ℚ[X]) :
    ∑ a ∈ Finset.range m, bernoulliFunctional (Q.comp (C (a : ℚ) + C (m : ℚ) * X)) =
      m * bernoulliFunctional Q := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.add_comp, map_add, Finset.sum_add_distrib, hp, hq, mul_add]
  | monomial n c =>
    have hterm (a : ℕ) : bernoulliFunctional ((Polynomial.monomial n c).comp
        (C (a : ℚ) + C (m : ℚ) * X)) =
        c * (m : ℚ) ^ n * (Polynomial.bernoulli n).eval ((a : ℚ) / m) := by
      have hx : (C (a : ℚ) + C (m : ℚ) * X) ^ n =
          C ((m : ℚ) ^ n) * (X + C ((a : ℚ) / m)) ^ n := by
        rw [Polynomial.C_pow, ← mul_pow, mul_add, ← Polynomial.C_mul, mul_div_cancel₀ _ hm',
          add_comm]
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_pow_comp, hx, ← mul_assoc, ← Polynomial.C_mul,
        ← Polynomial.smul_eq_C_mul, map_smul, bernoulliFunctional_X_add_C_pow, smul_eq_mul]
    simp only [hterm, ← Finset.mul_sum, mul_assoc, bernoulli_eval_distribution n hm,
      bernoulliFunctional_monomial, ← bernoulliFunctional_X_add_C_pow n 0, map_zero, add_zero,
      bernoulliFunctional_X_pow]
    ring

end Zeta5Irr
