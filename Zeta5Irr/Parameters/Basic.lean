/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs

/-!
# The parameters of the construction, and `ξ` as a series

The determinant construction is a one‑parameter family: a positive integer `n` fixes a
pole bound `K = 40 n`, an inner degree `N = 3 n` and a matrix order `h = 37 n`, and every
estimate of the method is governed not by these three numbers but by their ratios to `K`,
namely `α = N / K = 3/40`, `λ = h / K = 37/40` and `H = (h + 3 N) / K = 1 + 2 α = 23/20`.
The ratios are rational, and the identities `λ = 1 - α` and `H = λ + 3 α` are the two
arithmetic coincidences the choice `40, 3, 37` is made for.

This file also identifies the real number `ξ = ζ(5)` with the series it is the sum of,
`ξ = ∑_{v ≥ 1} v⁻⁵`. The point `s = 5` lies in the half‑plane of absolute convergence, so
the zeta function is given there by its Dirichlet series, and that series has real terms.

## Main definitions

* `Zeta5Irr.poleBound`: the pole bound `K = 40 n`.
* `Zeta5Irr.innerDegree`: the inner degree `N = 3 n`.
* `Zeta5Irr.matrixOrder`: the matrix order `h = 37 n`.
* `Zeta5Irr.innerRatio`, `Zeta5Irr.orderRatio`, `Zeta5Irr.heightRatio`: the ratios
  `α = 3/40`, `λ = 37/40` and `H = 23/20`.

## Main results

* `Zeta5Irr.zetaFive_eq_tsum`: `ξ = ∑_{v ≥ 1} v⁻⁵`.
* `Zeta5Irr.orderRatio_eq_one_sub_innerRatio`,
  `Zeta5Irr.heightRatio_eq_one_add_two_mul_innerRatio`,
  `Zeta5Irr.orderRatio_add_three_mul_innerRatio`: `λ = 1 - α`, `H = 1 + 2 α` and `λ + 3 α = H`.
* `Zeta5Irr.innerRatio_mul_poleBound`, `Zeta5Irr.orderRatio_mul_poleBound`,
  `Zeta5Irr.heightRatio_mul_poleBound`: `α K = N`, `λ K = h` and `H K = h + 3 N`.
* `Zeta5Irr.matrixOrder_add_innerDegree`, `Zeta5Irr.poleBound_sub_innerDegree`:
  `h + N = K` and `K - N = h`, so `h` is the number of far poles `N < j ≤ K`.

## Implementation notes

* The source's names for the six parameters are the single letters `K`, `N`, `h`, `α`, `λ`
  and `H`. They cannot be used here: `h` and `H` would differ only in case, `H` is also the
  source's own name for the harmonic sums `H_j^{(5)}`, and a global constant called `h` or
  `N` collides with the commonest name of a hypothesis and with that of a variable. Each
  parameter is therefore named for its role in the construction, and the correspondence
  with the source is recorded in its docstring.
* The three integer parameters are functions of `n` rather than variables fixed by a
  section, because most of the later estimates hold for an arbitrary multiple `K` of `40`
  and mention `n` only through `K`. Nothing forces `n` to be positive at the point of
  definition; the lemmas that need it say so.
* The ratios are rational, as in the source, and are coerced where a real inequality
  needs them. Their values are numerals, so a numerical claim about them — `6 α = 9/20`,
  say — is `norm_num [innerRatio]`.
* In `zetaFive_eq_tsum` the sum ranges over all `v : ℕ`; the `v = 0` term is
  `1 / 0 ^ 5 = 0`, so the series is the source's `∑_{v ≥ 1} v⁻⁵`.
* The source's proof takes the real part of a convergent complex series term by term.
  The formal proof instead exhibits the complex sum as the coercion of the real sum,
  through `Complex.ofReal_tsum`, which needs no summability hypothesis; summability is a
  separate statement, `Zeta5Irr.summable_one_div_nat_pow_five`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1, equation (2.1): the parameters.
-/

@[expose] public section

namespace Zeta5Irr

/-! ### The parameters -/

/-- The pole bound `K = 40 n`: the functional of the construction is applied to rational
functions whose poles are the `K` numbers `-j ^ 2` for `1 ≤ j ≤ K`. -/
@[zeta5irr "not_params"]
def poleBound (n : ℕ) : ℕ := 40 * n

/-- The inner degree `N = 3 n`: the degree of the pole product `D_N`, whose sixth power is
the numerator of the rational functions the Hankel matrix is built from. -/
@[zeta5irr "not_params"]
def innerDegree (n : ℕ) : ℕ := 3 * n

/-- The matrix order `h = 37 n`: the number of rows of the Hankel matrix `G_K`, equal to
the number `K - N` of poles that survive in its entries. -/
@[zeta5irr "not_params"]
def matrixOrder (n : ℕ) : ℕ := 37 * n

/-- The inner ratio `α = 3/40`, the value of `N / K`. -/
@[zeta5irr "not_params"]
def innerRatio : ℚ := 3 / 40

/-- The order ratio `λ = 37/40`, the value of `h / K`. -/
@[zeta5irr "not_params"]
def orderRatio : ℚ := 37 / 40

/-- The height ratio `H = 1 + 2 α = 23/20`, the value of `(h + 3 N) / K`. -/
@[zeta5irr "not_params"]
def heightRatio : ℚ := 23 / 20

/-! ### The integer parameters -/

variable {n : ℕ}

/-- The pole bound `K = 40 n` is positive for positive `n`. -/
theorem poleBound_pos (hn : 0 < n) : 0 < poleBound n := by
  simpa [poleBound] using hn

/-- The inner degree `N = 3 n` is positive for positive `n`. -/
theorem innerDegree_pos (hn : 0 < n) : 0 < innerDegree n := by
  simpa [innerDegree] using hn

/-- The matrix order `h = 37 n` is positive for positive `n`. -/
theorem matrixOrder_pos (hn : 0 < n) : 0 < matrixOrder n := by
  simpa [matrixOrder] using hn

/-- `40` divides the pole bound `K`. -/
@[simp]
theorem forty_dvd_poleBound (n : ℕ) : 40 ∣ poleBound n :=
  Dvd.intro n rfl

/-- `h + N = K`. -/
theorem matrixOrder_add_innerDegree (n : ℕ) : matrixOrder n + innerDegree n = poleBound n := by
  simp only [matrixOrder, innerDegree, poleBound]
  ring

/-- `K - N = h`. -/
theorem poleBound_sub_innerDegree (n : ℕ) : poleBound n - innerDegree n = matrixOrder n := by
  simp only [poleBound, innerDegree, matrixOrder]
  omega

/-- `N ≤ K`. -/
theorem innerDegree_le_poleBound (n : ℕ) : innerDegree n ≤ poleBound n :=
  le_of_add_le_right (matrixOrder_add_innerDegree n).le

/-- `N < K` for positive `n`. -/
theorem innerDegree_lt_poleBound (hn : 0 < n) : innerDegree n < poleBound n := by
  simp only [innerDegree, poleBound]
  omega

/-! ### The ratios -/

/-- `0 < α`. -/
theorem innerRatio_pos : 0 < innerRatio := by norm_num [innerRatio]

/-- `α < 1`. -/
theorem innerRatio_lt_one : innerRatio < 1 := by norm_num [innerRatio]

/-- `0 < λ`. -/
theorem orderRatio_pos : 0 < orderRatio := by norm_num [orderRatio]

/-- `λ < 1`. -/
theorem orderRatio_lt_one : orderRatio < 1 := by norm_num [orderRatio]

/-- `1 < H`. -/
theorem one_lt_heightRatio : 1 < heightRatio := by norm_num [heightRatio]

/-- `λ = 1 - α`. -/
theorem orderRatio_eq_one_sub_innerRatio : orderRatio = 1 - innerRatio := by
  norm_num [orderRatio, innerRatio]

/-- `H = 1 + 2 α`. -/
theorem heightRatio_eq_one_add_two_mul_innerRatio : heightRatio = 1 + 2 * innerRatio := by
  norm_num [heightRatio, innerRatio]

/-- `λ + 3 α = H`. -/
theorem orderRatio_add_three_mul_innerRatio : orderRatio + 3 * innerRatio = heightRatio := by
  norm_num [orderRatio, innerRatio, heightRatio]

/-- `α K = N`. -/
theorem innerRatio_mul_poleBound (n : ℕ) :
    innerRatio * (poleBound n : ℚ) = (innerDegree n : ℚ) := by
  simp only [innerRatio, poleBound, innerDegree, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- `λ K = h`. -/
theorem orderRatio_mul_poleBound (n : ℕ) :
    orderRatio * (poleBound n : ℚ) = (matrixOrder n : ℚ) := by
  simp only [orderRatio, poleBound, matrixOrder, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- `H K = h + 3 N`. -/
theorem heightRatio_mul_poleBound (n : ℕ) :
    heightRatio * (poleBound n : ℚ) = (matrixOrder n : ℚ) + 3 * (innerDegree n : ℚ) := by
  simp only [heightRatio, poleBound, matrixOrder, innerDegree, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-! ### `ξ` as a series -/

/-- The series `∑_{v} 1 / v ^ 5` of real numbers is summable. -/
theorem summable_one_div_nat_pow_five : Summable fun v : ℕ => 1 / (v : ℝ) ^ 5 :=
  Real.summable_one_div_nat_pow.2 (by norm_num)

/-- `ξ = ∑_{v ≥ 1} v⁻⁵`. The sum is over all `v : ℕ`, the term at `v = 0` being zero. -/
@[zeta5irr "lem_zeta5_tsum"]
theorem zetaFive_eq_tsum : zetaFive = ∑' v : ℕ, 1 / (v : ℝ) ^ 5 := by
  have h : riemannZeta 5 = ((∑' v : ℕ, 1 / (v : ℝ) ^ 5 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    exact_mod_cast zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  rw [zetaFive, h, Complex.ofReal_re]

/-- `ξ = ∑_{v ≥ 1} v⁻⁵`, with the terms written as `(v ^ 5)⁻¹`. -/
theorem zetaFive_eq_tsum_inv : zetaFive = ∑' v : ℕ, ((v : ℝ) ^ 5)⁻¹ := by
  simpa [one_div] using zetaFive_eq_tsum

end Zeta5Irr
