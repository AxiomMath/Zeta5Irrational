/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.LocalEstimates.Rowpoly

/-!
# The pulled-back integrand `g_{a,i,c,j}`

For an odd prime `p`, an integer `M ≥ 40`, `K = 40 n`, indices `0 ≤ a, c ≤ m°` and integers
`0 ≤ i < L_a`, `0 ≤ j < L_c`, the entry valuations of the inner range are read off the polynomial
`g_{a,i,c,j}(x) = (-1)^{K-N} x^5 D_N(-x^2)^5 Ψ_{a,i}(-x^2) Ψ_{c,j}(-x^2) ∈ ℚ[x]`,
obtained by pulling the integrand back along the substitution `t = -x^2`.

## Main definitions

* `Zeta5Irr.pulledIntegrand`: the polynomial `g_{a,i,c,j} ∈ ℚ[x]`.

## Main results

* `Zeta5Irr.eval_pulledIntegrand`: the value of `g_{a,i,c,j}` at a rational `x`.
* `Zeta5Irr.pulledIntegrand_comm`: `g_{a,i,c,j} = g_{c,j,a,i}`.
* `Zeta5Irr.pulledIntegrand_comp_neg_X`: `g_{a,i,c,j}` is odd, `g(-x) = -g(x)`.

## Implementation notes

* `K = 40 n` and `N = 3 n` are `poleBound n` and `innerDegree n`, so `g_{a,i,c,j}` takes `n` as
  an argument; the exponent `K - N = 37 n` is a natural number.
* The hypotheses that `p` is an odd prime, `M ≥ 40`, `a, c ≤ m°`, `i < L_a` and `j < L_c` are not
  needed to define `g_{a,i,c,j}`; they are carried by the lemmas which use them.
* The polynomial is an element of `ℚ[X]`, the composites `D_N(-x^2)` and `Ψ_{a,i}(-x^2)` being
  `Polynomial.comp` with `-X^2`, so that it may be evaluated in any `ℚ`-algebra, e.g. `ℚ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The pulled-back integrand
`g_{a,i,c,j}(x) = (-1)^{K-N} x^5 D_N(-x^2)^5 Ψ_{a,i}(-x^2) Ψ_{c,j}(-x^2)`,
where `K = 40 n` and `N = 3 n`. -/
@[zeta5irr "def_in_pull"]
noncomputable def pulledIntegrand (n p M a i c j : ℕ) : ℚ[X] :=
  C ((-1 : ℚ) ^ (poleBound n - innerDegree n)) * X ^ 5 *
    (poleProductRange (innerDegree n) ℚ).comp (-X ^ 2) ^ 5 *
    (rowPoly n p M a i).comp (-X ^ 2) * (rowPoly n p M c j).comp (-X ^ 2)

/-- Unfolding lemma for `pulledIntegrand`. -/
theorem pulledIntegrand_def (n p M a i c j : ℕ) : pulledIntegrand n p M a i c j =
    C ((-1 : ℚ) ^ (poleBound n - innerDegree n)) * X ^ 5 *
      (poleProductRange (innerDegree n) ℚ).comp (-X ^ 2) ^ 5 *
      (rowPoly n p M a i).comp (-X ^ 2) * (rowPoly n p M c j).comp (-X ^ 2) :=
  rfl

/-- The sign `(-1)^{K - N}` equals `(-1)^n`, since `K - N = 37 n`. -/
theorem neg_one_pow_poleBound_sub_innerDegree (n : ℕ) :
    (-1 : ℚ) ^ (poleBound n - innerDegree n) = (-1) ^ n := by
  have h : poleBound n - innerDegree n = 2 * (18 * n) + n := by
    simp only [poleBound, innerDegree]; omega
  rw [h, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The value of `g_{a,i,c,j}` at `x`:
`(-1)^{K-N} x^5 D_N(-x^2)^5 Ψ_{a,i}(-x^2) Ψ_{c,j}(-x^2)`. -/
@[simp]
theorem eval_pulledIntegrand (n p M a i c j : ℕ) (x : ℚ) :
    (pulledIntegrand n p M a i c j).eval x =
      (-1) ^ (poleBound n - innerDegree n) * x ^ 5 *
        (poleProductRange (innerDegree n) ℚ).eval (-x ^ 2) ^ 5 *
        (rowPoly n p M a i).eval (-x ^ 2) * (rowPoly n p M c j).eval (-x ^ 2) := by
  simp [pulledIntegrand_def, eval_comp]

/-- `g_{a,i,c,j}` is symmetric under exchanging `(a, i)` and `(c, j)`. -/
theorem pulledIntegrand_comm (n p M a i c j : ℕ) :
    pulledIntegrand n p M a i c j = pulledIntegrand n p M c j a i := by
  simp only [pulledIntegrand_def]; ring

/-- `g_{a,i,c,j}` is an odd polynomial: `g(-x) = -g(x)`. -/
theorem pulledIntegrand_comp_neg_X (n p M a i c j : ℕ) :
    (pulledIntegrand n p M a i c j).comp (-X) = -pulledIntegrand n p M a i c j := by
  have h : ((-X ^ 2 : ℚ[X])).comp (-X) = -X ^ 2 := by simp
  simp only [pulledIntegrand_def, mul_comp, pow_comp, C_comp, X_comp, comp_assoc, h]
  ring

end Zeta5Irr
