/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.DerivativeNumerators
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Tactic.ENatToNat

/-!
# The derivatives of `1 / (e^{2πy} - 1)`

With `q = e^{-2πy}` one has `1 / (e^{2πy} - 1) = q / (1 - q)` and `dq/dy = -2π q`. Writing
`G_k(q) = q Φ_k(q) / (1 - q)^{k+1}` for the derivative numerators `Φ_k`, the quotient rule and
the recurrence `Φ_{k+1} = (q Φ_k)' (1 - q) + (k + 1) q Φ_k` give `q G_k'(q) = G_{k+1}(q)`, so
that by induction
`(d/dy)^k 1 / (e^{2πy} - 1) = (-2π)^k e^{-2πy} Φ_k(e^{-2πy}) / (1 - e^{-2πy})^{k+1}`
for every `y ≠ 0`.

## Main results

* `Zeta5Irr.one_div_exp_sub_one_eq_div`: `1 / (e^{2πy} - 1) = q / (1 - q)` with
  `q = e^{-2πy}`.
* `Zeta5Irr.hasDerivAt_expDerivForm`: the derivative of the `k`-th formula is the
  `(k + 1)`-st.
* `Zeta5Irr.iteratedDeriv_one_div_exp_sub_one`: the closed form of the `k`-th derivative.

## Implementation notes

The source states the formula for `0 ≤ k ≤ 4` and `y > 0`. The proof by induction works for
every `k`, and away from the pole `y = 0` on both sides, so the result is stated for every
`k : ℕ` and every `y ≠ 0`. The derivative is Mathlib's `iteratedDeriv` of the function on all
of `ℝ`; since `{y ≠ 0}` is open, this is determined locally.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Real Polynomial

namespace Zeta5Irr

/-- For every real `y`, `1 / (e^{2πy} - 1) = e^{-2πy} / (1 - e^{-2πy})` (both sides vanish at
`y = 0` under Lean's division). -/
theorem one_div_exp_sub_one_eq_div (y : ℝ) :
    1 / (Real.exp (2 * π * y) - 1) = Real.exp (-2 * π * y) / (1 - Real.exp (-2 * π * y)) := by
  have h : Real.exp (-2 * π * y) * Real.exp (2 * π * y) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hne : Real.exp (-2 * π * y) ≠ 0 := (Real.exp_pos _).ne'
  rw [← mul_div_mul_left 1 _ hne, mul_one, mul_sub, h, mul_one]

/-- The derivative of `(-2π)^k e^{-2πy} Φ_k(e^{-2πy}) / (1 - e^{-2πy})^{k+1}` at `y ≠ 0`
is the same expression with `k + 1` in place of `k`. -/
theorem hasDerivAt_expDerivForm (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y ↦ (-2 * π) ^ k *
        (Real.exp (-2 * π * y) * aeval (Real.exp (-2 * π * y)) (derivNumerator k)) /
        (1 - Real.exp (-2 * π * y)) ^ (k + 1))
      ((-2 * π) ^ (k + 1) *
        (Real.exp (-2 * π * y) * aeval (Real.exp (-2 * π * y)) (derivNumerator (k + 1))) /
        (1 - Real.exp (-2 * π * y)) ^ (k + 1 + 1)) y := by
  have hq1 : 1 - Real.exp (-2 * π * y) ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, Real.exp_eq_one_iff]
    have := Real.pi_pos
    intro h
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact hy h
  have hexp : HasDerivAt (fun y ↦ Real.exp (-2 * π * y))
      (Real.exp (-2 * π * y) * (-2 * π)) y := by
    have := ((hasDerivAt_id' y).const_mul (-2 * π)).exp
    rwa [mul_one] at this
  have hnum : HasDerivAt (fun y ↦ Real.exp (-2 * π * y) *
      aeval (Real.exp (-2 * π * y)) (derivNumerator k))
      (aeval (Real.exp (-2 * π * y)) (derivative (X * derivNumerator k)) *
        (Real.exp (-2 * π * y) * (-2 * π))) y := by
    have := (Polynomial.hasDerivAt_aeval (X * derivNumerator k) _).comp y hexp
    simpa only [Function.comp_def, map_mul, aeval_X] using this
  have hden := (hexp.const_sub 1).fun_pow (k + 1)
  rw [Nat.add_sub_cancel] at hden
  have := (hnum.div hden (pow_ne_zero _ hq1)).const_mul ((-2 * π) ^ k)
  convert this using 1
  · ext y; simp only [Pi.div_apply, mul_div_assoc]
  · rw [derivNumerator_succ]
    simp only [map_add, map_mul, map_sub, map_one, aeval_X, map_natCast]
    generalize Real.exp (-2 * π * y) = q at hq1 ⊢
    field_simp
    push_cast
    ring

/-- **The derivatives of `1 / (e^{2πy} - 1)`.** For every `k` and every `y ≠ 0`,
`(d/dy)^k 1 / (e^{2πy} - 1) = (-2π)^k e^{-2πy} Φ_k(e^{-2πy}) / (1 - e^{-2πy})^{k+1}`. -/
@[zeta5irr "lem_w_f_form"]
theorem iteratedDeriv_one_div_exp_sub_one (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    iteratedDeriv k (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) y =
      (-2 * π) ^ k *
        (Real.exp (-2 * π * y) * aeval (Real.exp (-2 * π * y)) (derivNumerator k)) /
        (1 - Real.exp (-2 * π * y)) ^ (k + 1) := by
  induction k generalizing y with
  | zero =>
    simp only [iteratedDeriv_zero, derivNumerator_zero, map_one, mul_one, pow_zero, one_mul,
      zero_add, pow_one]
    exact one_div_exp_sub_one_eq_div y
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun y ↦ 1 / (Real.exp (2 * π * y) - 1)) =ᶠ[nhds y]
        fun y ↦ (-2 * π) ^ k *
          (Real.exp (-2 * π * y) * aeval (Real.exp (-2 * π * y)) (derivNumerator k)) /
          (1 - Real.exp (-2 * π * y)) ^ (k + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz using ih hz
    rw [hev.deriv_eq, (hasDerivAt_expDerivForm k hy).deriv]

end Zeta5Irr
