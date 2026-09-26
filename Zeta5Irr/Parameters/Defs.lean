/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Rat.Star
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# Parameters, the functional, and the matrix

This file fixes the arithmetic data the irrationality proof is built from: the
real number `ξ = ζ(5)`, the partial sums `H_j^{(5)} = ∑_{v = 1}^{j} v⁻⁵` of the
series representing it, the monic polynomial `D_S(t) = ∏_{j ∈ S} (t + j ^ 2)`
whose roots are the poles `-j ^ 2` for `j ∈ S`, and the Bernoulli moments
`m(e) = (-1) ^ e B_{2e + 2} (2e + 3)(2e + 4)(2e + 5) / 24`.

The moments are the values on the monomials `t ^ e` of the rational functional
of the method, and `H_j^{(5)}` enters through its values on the simple poles
`1 / (t + j ^ 2)`; the polynomial `D_S` is the common denominator of the
rational functions the functional is applied to, so that the entries of the
Hankel matrix of the construction are values of the functional at
`D_N(t) ^ 6 t ^ {i + j} / D_K(t)`. Nothing here is an estimate: every
declaration is a definition or a structural property of one.

## Main definitions

* `Zeta5Irr.zetaFive`: the real number `ξ = ζ(5)`.
* `Zeta5Irr.harmonicFive`: the harmonic sum of order five, `H_j^{(5)}`.
* `Zeta5Irr.poleProduct`: the pole product `D_S`.
* `Zeta5Irr.bernoulliMoment`: the Bernoulli moment `m(e)`.

## Main results

* `Zeta5Irr.harmonicFive_succ`: the recurrence `H_{j+1}^{(5)} = H_j^{(5)} + (j + 1)⁻⁵`.
* `Zeta5Irr.monic_poleProduct`, `Zeta5Irr.natDegree_poleProduct`,
  `Zeta5Irr.degree_poleProduct`: `D_S` is monic of degree `#S`.
* `Zeta5Irr.eval_poleProduct`, `Zeta5Irr.aeval_poleProduct`, `Zeta5Irr.map_poleProduct`,
  `Zeta5Irr.derivative_poleProduct`: the value (at a point of the coefficient ring, or of
  an algebra over it), the base change, and the derivative `D_S' = ∑_{j ∈ S} D_{S \ {j}}`
  of the pole product.
* `Zeta5Irr.eval_derivative_poleProduct`, `Zeta5Irr.eval_derivative_poleProduct_neg_sq`: the
  derivative at a root, `D_S'(-j²) = D_{S \ {j}}(-j²) = ∏_{k ∈ S \ {j}} (k² - j²)`.

## Implementation notes

* The source fixes the convention `B₁ = -1/2` for the Bernoulli numbers, which
  is Mathlib's `bernoulli` (as opposed to `bernoulli'`). Only the even indices
  `2e + 2 ≥ 2` occur in a moment, and there the two conventions agree, so the
  convention is immaterial for `bernoulliMoment`; it matters for the
  Bernoulli-polynomial identities used later.
* The source indexes the pole product by a finite `S ⊆ ℤ_{>0}` and works in
  `ℚ[t]`. Here the index set is a `Finset ℕ` and the coefficients lie in an
  arbitrary commutative semiring: positivity of the indices is not needed to
  define the product (the index `0` contributes the factor `t`), and the
  construction is used over `ℚ`, over `ℝ` after evaluation at real points, and
  over `ℚ_p`, related by `Zeta5Irr.map_poleProduct`.
* `zetaFive` is an `abbrev`: it names the real part of `riemannZeta 5` and has
  no content beyond that name, so every statement about `ξ` is, reducibly, a
  statement about `(riemannZeta 5).re`. Its series representation
  `ξ = ∑_{v ≥ 1} v⁻⁵` is a separate result.
* `harmonicFive` fixes the order five instead of carrying the order as a
  parameter, since no other order occurs; the order-one case is Mathlib's
  `harmonic`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and
  the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- `ξ`, the value of the Riemann zeta function at `s = 5`, as a real number. -/
@[zeta5irr "def_zeta5"]
noncomputable abbrev zetaFive : ℝ := (riemannZeta 5).re

/-- The harmonic sum of order five, `H_j^{(5)} = ∑_{v = 1}^{j} v⁻⁵`. -/
@[zeta5irr "def_harm5"]
def harmonicFive (j : ℕ) : ℚ := ∑ v ∈ Icc 1 j, ((v : ℚ) ^ 5)⁻¹

/-- The harmonic sum of order five is zero at `j = 0`: `H_0^{(5)} = 0`. -/
@[simp]
theorem harmonicFive_zero : harmonicFive 0 = 0 := by
  simp [harmonicFive]

/-- The recurrence `H_{j+1}^{(5)} = H_j^{(5)} + (j + 1)⁻⁵`. -/
theorem harmonicFive_succ (j : ℕ) :
    harmonicFive (j + 1) = harmonicFive j + (((j : ℚ) + 1) ^ 5)⁻¹ := by
  rw [harmonicFive, harmonicFive, sum_Icc_succ_top (Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero j))]
  push_cast
  ring

/-- The harmonic sum of order five is nonnegative. -/
theorem harmonicFive_nonneg (j : ℕ) : 0 ≤ harmonicFive j :=
  sum_nonneg fun _ _ ↦ by positivity

/-- The harmonic sum of order five `H_j^{(5)}` is positive for `j ≠ 0`. -/
theorem harmonicFive_pos {j : ℕ} (hj : j ≠ 0) : 0 < harmonicFive j :=
  sum_pos' (fun _ _ ↦ by positivity)
    ⟨1, mem_Icc.2 ⟨le_rfl, Nat.one_le_iff_ne_zero.2 hj⟩, by norm_num⟩

/-- The harmonic sum of order five is monotone in `j`. -/
theorem monotone_harmonicFive : Monotone harmonicFive := fun _ _ h ↦
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ _ _ ↦ by positivity

section PoleProduct

open Polynomial

/-- The pole product `D_S(t) = ∏_{j ∈ S} (t + j ^ 2)`: the monic polynomial
whose roots are the poles `-j ^ 2`, `j ∈ S`. -/
@[zeta5irr "def_Dset"]
noncomputable def poleProduct (S : Finset ℕ) (R : Type*) [CommSemiring R] : R[X] :=
  ∏ j ∈ S, (X + C ((j : R) ^ 2))

variable (S : Finset ℕ) (R : Type*) [CommSemiring R]

/-- The pole product over the empty set is `1`. -/
@[simp]
theorem poleProduct_empty : poleProduct ∅ R = 1 := by
  rw [poleProduct, prod_empty]

/-- For `j ∉ S`, `D_{S ∪ {j}}(t) = (t + j ^ 2) D_S(t)`. -/
theorem poleProduct_insert {j : ℕ} {S : Finset ℕ} (h : j ∉ S) :
    poleProduct (insert j S) R = (X + C ((j : R) ^ 2)) * poleProduct S R := by
  rw [poleProduct, poleProduct, prod_insert h]

/-- The pole product `D_S` is monic. -/
theorem monic_poleProduct : (poleProduct S R).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- Over a nontrivial semiring, the pole product `D_S` is nonzero. -/
theorem poleProduct_ne_zero [Nontrivial R] : poleProduct S R ≠ 0 :=
  (monic_poleProduct S R).ne_zero

/-- The value of the pole product at `t ∈ R`: `D_S(t) = ∏_{j ∈ S} (t + j ^ 2)`. -/
@[simp]
theorem eval_poleProduct (t : R) : (poleProduct S R).eval t = ∏ j ∈ S, (t + (j : R) ^ 2) := by
  simp only [poleProduct, eval_prod, eval_add, eval_X, eval_C]

/-- Over a nontrivial semiring, the pole product `D_S` has natural degree `#S`. -/
@[simp]
theorem natDegree_poleProduct [Nontrivial R] : (poleProduct S R).natDegree = #S := by
  rw [poleProduct, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]

/-- Over a nontrivial semiring, the pole product `D_S` has degree `#S`. -/
theorem degree_poleProduct [Nontrivial R] : (poleProduct S R).degree = #S := by
  rw [degree_eq_natDegree (poleProduct_ne_zero S R), natDegree_poleProduct]

/-- The image of the pole product over `R` under a ring hom `R →+* R'` is the pole product
over `R'`. -/
theorem map_poleProduct {R' : Type*} [CommSemiring R'] (f : R →+* R') :
    (poleProduct S R).map f = poleProduct S R' := by
  simp [poleProduct, Polynomial.map_prod]

/-- The value of the pole product at a point of an `R`-algebra:
`D_S(t) = ∏_{j ∈ S} (t + j ^ 2)`. -/
@[simp]
theorem aeval_poleProduct {A : Type*} [CommSemiring A] [Algebra R A] (t : A) :
    aeval t (poleProduct S R) = ∏ j ∈ S, (t + (j : A) ^ 2) := by
  simp [poleProduct, map_prod]

/-- The derivative of the pole product: `D_S' = ∑_{j ∈ S} D_{S \ {j}}`, since every
factor of `D_S` is monic of degree one. -/
theorem derivative_poleProduct :
    derivative (poleProduct S R) = ∑ j ∈ S, poleProduct (S.erase j) R := by
  rw [poleProduct, derivative_prod_finset]
  exact sum_congr rfl fun j _ ↦ by rw [derivative_X_add_C, mul_one, poleProduct]

end PoleProduct

section PoleProductRoots

open Polynomial

variable {R : Type*} [CommRing R]

/-- Each `-j ^ 2` with `j ∈ T` is a root of the pole product `D_T`. -/
theorem eval_neg_sq_poleProduct_of_mem {T : Finset ℕ} {j : ℕ} (hj : j ∈ T) :
    (poleProduct T R).eval (-(j : R) ^ 2) = 0 := by
  rw [eval_poleProduct]
  exact prod_eq_zero hj (by ring)

/-- The derivative of the pole product at a root: `D_S'(-j ^ 2) = D_{S \ {j}}(-j ^ 2)`. -/
theorem eval_derivative_poleProduct (S : Finset ℕ) {j : ℕ} (hj : j ∈ S) :
    (derivative (poleProduct S R)).eval (-(j : R) ^ 2) =
      (poleProduct (S.erase j) R).eval (-(j : R) ^ 2) := by
  rw [derivative_poleProduct, eval_finsetSum, sum_eq_single_of_mem j hj]
  intro k hk hkj
  exact eval_neg_sq_poleProduct_of_mem (mem_erase.2 ⟨Ne.symm hkj, hj⟩)

/-- The derivative of the pole product at a root: `D_S'(-r₀²) = ∏_{r ∈ S \ {r₀}} (r² - r₀²)`
for `r₀ ∈ S`. -/
theorem eval_derivative_poleProduct_neg_sq {S : Finset ℕ} {r₀ : ℕ} (h : r₀ ∈ S) :
    (derivative (poleProduct S R)).eval (-(r₀ : R) ^ 2) =
      ∏ r ∈ S.erase r₀, ((r : R) ^ 2 - r₀ ^ 2) := by
  rw [eval_derivative_poleProduct S h, eval_poleProduct]
  exact prod_congr rfl fun _ _ ↦ by ring

end PoleProductRoots

/-- The Bernoulli moment
`m(e) = (-1) ^ e B_{2e + 2} (2e + 3)(2e + 4)(2e + 5) / 24`, the value of the
functional of the construction on the monomial `t ^ e`. -/
@[zeta5irr "def_moment"]
def bernoulliMoment (e : ℕ) : ℚ :=
  (-1) ^ e * _root_.bernoulli (2 * e + 2) * (2 * e + 3) * (2 * e + 4) * (2 * e + 5) / 24

/-- The Bernoulli moment at `e = 0`: `m(0) = 5 / 12`. -/
theorem bernoulliMoment_zero : bernoulliMoment 0 = 5 / 12 := by
  norm_num [bernoulliMoment, bernoulli]

/-- The Bernoulli moment at `e = 1`: `m(1) = 7 / 24`. -/
theorem bernoulliMoment_one : bernoulliMoment 1 = 7 / 24 := by
  norm_num [bernoulliMoment, bernoulli]

end Zeta5Irr
