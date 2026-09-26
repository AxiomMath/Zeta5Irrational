/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.PoleSumBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

/-!
# Partial fractions for the exponential factor

For `y > 0`,
`1 / (exp (2πy) - 1) = -1/2 + 1 / (2πy) + (1/π) ∑_{v ≥ 1} y / (y² + v²)`.

This is the Mittag-Leffler expansion of the cotangent, `π cot (πx) = 1/x + ∑_{n ≥ 1}
(1/(x - n) + 1/(x + n))`, evaluated at the purely imaginary point `x = iy`. There each pair
of terms is `-i · 2y / (y² + n²)`, while `cot (πiy) = -i (1 + q) / (1 - q)` with
`q = exp (-2πy)`; comparing and cancelling `-i` gives
`π (1 + q) / (1 - q) = 1/y + 2 ∑_{v ≥ 1} y / (y² + v²)`, which rearranges to the claim.

## Main results

* `Zeta5Irr.one_div_exp_sub_one_eq`: the partial fraction expansion of `1 / (exp (2πy) - 1)`.
* `Zeta5Irr.hasSum_div_sq_add_succ_sq`: the same identity, read as the value of the
  convergent series `∑_{v ≥ 1} y / (y² + v²)`.

## Implementation notes

The sum over `v ≥ 1` is written as a sum over `v : ℕ` of the term at `v + 1`. The identity is
stated with `tsum`, which needs no convergence hypothesis; convergence of the series (from the
uniform bound on its partial sums) is what upgrades it to the `HasSum` form.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2 (the weight, positivity, and the degree).
-/

@[expose] public section

open Real Complex

namespace Zeta5Irr

/-- **Partial fractions for the exponential factor.** For `y > 0`,
`1 / (exp (2πy) - 1) = -1/2 + 1 / (2πy) + (1/π) ∑_{v ≥ 1} y / (y² + v²)`. -/
@[zeta5irr "lem_w_coth"]
theorem one_div_exp_sub_one_eq {y : ℝ} (hy : 0 < y) :
    1 / (Real.exp (2 * π * y) - 1) =
      -1 / 2 + 1 / (2 * π * y) + 1 / π * ∑' v : ℕ, y / (y ^ 2 + ((v : ℝ) + 1) ^ 2) := by
  have hmem : I * y ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp only [intCast_im, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul,
      zero_add] at this
    exact hy.ne' this.symm
  have h := cot_series_rep' hmem
  have hterm : ∀ n : ℕ, 1 / (I * y - (n + 1)) + 1 / (I * y + (n + 1)) =
      ((-2 * (y / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ) * I := by
    intro n
    have h1 : I * y - (n + 1) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have h2 : I * y + (n + 1) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have h3 : ((y : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2) ≠ 0 := by
      exact_mod_cast (by positivity : (y ^ 2 + ((n : ℝ) + 1) ^ 2) ≠ 0)
    push_cast
    field_simp
    ring_nf
    simp
  simp_rw [hterm] at h
  rw [tsum_mul_right, ← Complex.ofReal_tsum, tsum_mul_left] at h
  set S := ∑' v : ℕ, y / (y ^ 2 + ((v : ℝ) + 1) ^ 2)
  rw [Complex.cot_pi_eq_exp_ratio] at h
  have hq : Complex.exp (2 * π * I * (I * y)) = ((Real.exp (-(2 * π * y)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; simp [I_sq]
  rw [hq] at h
  have hq1 : Real.exp (-(2 * π * y)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [pi_pos])
  have hE : Real.exp (2 * π * y) * Real.exp (-(2 * π * y)) = 1 := by
    rw [← Real.exp_add]; simp
  set q := Real.exp (-(2 * π * y))
  set E := Real.exp (2 * π * y)
  have hq0 : (1 - q : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hq1).ne'
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have key : ((π * (1 + q) / (1 - q) - 1 / y : ℝ) : ℂ) = ((2 * S : ℝ) : ℂ) := by
    push_cast
    field_simp at h ⊢
    rw [I_sq] at h
    push_cast at h
    linear_combination h
  have key' : S = (π * (1 + q) / (1 - q) - 1 / y) / 2 := by
    have := Complex.ofReal_injective key
    linarith
  have hq1' : 0 < 1 - q := sub_pos.mpr hq1
  have hE1 : E - 1 ≠ 0 := by
    have : 1 < E := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  rw [key']
  field_simp
  linear_combination (-2 * π * y) * hE

/-- For `y > 0` the series `∑_{v ≥ 1} y / (y² + v²)` converges, with sum
`π / (exp (2πy) - 1) + π / 2 - 1 / (2y)`. -/
theorem hasSum_div_sq_add_succ_sq {y : ℝ} (hy : 0 < y) :
    HasSum (fun v : ℕ => y / (y ^ 2 + ((v : ℝ) + 1) ^ 2))
      (π / (Real.exp (2 * π * y) - 1) + π / 2 - 1 / (2 * y)) := by
  have hs : Summable fun v : ℕ => y / (y ^ 2 + ((v : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (summable_div_sq_add_sq hy)
    exact_mod_cast this
  convert hs.hasSum using 1
  rw [div_eq_mul_one_div π, one_div_exp_sub_one_eq hy]
  field_simp
  ring

end Zeta5Irr
