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
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

/-!
# The Andréief identity

Let `m` be a σ-finite measure on a measurable space `α`, let `ι` be a finite index type, and let
`f i, g j : α → 𝕜` (`i j : ι`) be functions such that every product `f i * g j` is integrable.
The *Andréief identity* (also called the Gram–Heine or Cauchy–Binet integral formula) states
that
`det [∫ f i * g j ∂m]_{i,j} = (1 / p!) ∫ det [f i (y k)]_{i,k} * det [g j (y l)]_{j,l} dmᵖ(y)`,
where `p` is the cardinality of `ι` and `mᵖ` is the product measure on `ι → α`.

Expanding both determinants on the right, the integrand is a signed sum of products
`∏ k, (f (τ k) * g (π k)) (y k)` over pairs of permutations `(τ, π)`. Each such product of
integrable one-variable functions is integrable for the product measure, and its integral is
`∏ k, ∫ f (τ k) * g (π k) ∂m`. Reindexing by `σ = π * τ⁻¹` shows that every `τ` contributes
exactly the Leibniz expansion of the left-hand side, so the sum over `τ` is `p!` times it.

## Main results

* `Zeta5Irr.integrable_det_mul_det`: the integrand `det [f i (y k)] * det [g j (y l)]` is
  integrable for the product measure.
* `Zeta5Irr.det_integral_mul_eq`: the Andréief identity.

## Implementation notes

* The blueprint states the identity for a positive Borel measure on `(0, ∞)`, real-valued Borel
  functions and index set `{1, …, p}` with `p ≥ 1`. Here the base space is an arbitrary
  measurable space, the scalars are any `RCLike` field, the index set is any finite type, and
  no measurability of the individual `f i`, `g j` is required: only integrability of the
  products `f i * g j`, which is the blueprint's hypothesis. A measure on `(0, ∞)` is obtained
  by taking `α = Set.Ioi 0`, or by taking a measure on `ℝ` supported on `(0, ∞)`.
* The product measure `mᵖ` is `MeasureTheory.Measure.pi`, which is defined for σ-finite
  factors; the identity is stated for σ-finite `m`, the setting in which the product measure
  on the right-hand side is determined by `m`.
* The proof avoids permuting the coordinates of the product measure: the reindexing
  `σ = π * τ⁻¹` is carried out after the integral has been factored into one-variable integrals.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3: the Gram integral and scaling.
* C. Andréief, *Note sur une relation entre les intégrales définies des produits des fonctions*,
  Mém. Soc. Sci. Phys. Nat. Bordeaux (3) 2 (1886), 1–14.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Matrix Finset

variable {α : Type*} {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- Pointwise expansion of the Andréief integrand: `det [f i (y k)] * det [g j (y l)]` is the
signed sum over pairs of permutations `(τ, π)` of `∏ k, f (τ k) (y k) * g (π k) (y k)`. -/
theorem det_mul_det_eq_sum (f g : ι → α → 𝕜) (y : ι → α) :
    (Matrix.of fun i k => f i (y k)).det * (Matrix.of fun j l => g j (y l)).det =
      ∑ τ : Equiv.Perm ι, ∑ π : Equiv.Perm ι,
        ((Equiv.Perm.sign τ : ℤ) : 𝕜) * ((Equiv.Perm.sign π : ℤ) : 𝕜) *
          ∏ k, (f (τ k) (y k) * g (π k) (y k)) := by
  rw [det_apply', det_apply', Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun π _ => ?_
  simp only [of_apply, Finset.prod_mul_distrib]
  ring

variable [MeasurableSpace α]

/-- The Andréief integrand `det [f i (y k)] * det [g j (y l)]` is integrable for the product
measure `mᵖ` as soon as every product `f i * g j` is `m`-integrable. -/
theorem integrable_det_mul_det (m : Measure α) [SigmaFinite m] (f g : ι → α → 𝕜)
    (hfg : ∀ i j, Integrable (fun y => f i y * g j y) m) :
    Integrable (fun y : ι → α =>
      (Matrix.of fun i k => f i (y k)).det * (Matrix.of fun j l => g j (y l)).det)
      (Measure.pi fun _ => m) := by
  simp_rw [det_mul_det_eq_sum]
  refine integrable_finsetSum _ fun τ _ => integrable_finsetSum _ fun π _ => ?_
  exact (Integrable.fintype_prod (f := fun k y => f (τ k) y * g (π k) y)
    fun k => hfg _ _).const_mul _

/-- Combinatorial core of the Andréief identity: for a square matrix `A`, the double signed sum
`∑ τ, ∑ π, ε(τ) ε(π) ∏ k, A (τ k) (π k)` equals `p! * det A`, where `p = card ι`. -/
theorem sum_sum_sign_mul_prod_eq (A : Matrix ι ι 𝕜) :
    ∑ τ : Equiv.Perm ι, ∑ π : Equiv.Perm ι,
        ((Equiv.Perm.sign τ : ℤ) : 𝕜) * ((Equiv.Perm.sign π : ℤ) : 𝕜) *
          ∏ k, A (τ k) (π k) =
      ((Fintype.card ι).factorial : 𝕜) * A.det := by
  have key : ∀ τ : Equiv.Perm ι, ∑ π : Equiv.Perm ι,
      ((Equiv.Perm.sign τ : ℤ) : 𝕜) * ((Equiv.Perm.sign π : ℤ) : 𝕜) *
        ∏ k, A (τ k) (π k) = A.det := by
    intro τ
    rw [← det_transpose, det_apply']
    refine (Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_).symm
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul,
      Equiv.Perm.coe_mul, Function.comp_apply, transpose_apply]
    rw [← Equiv.prod_comp τ (fun i => A i (σ i))]
    have hτ : ((Equiv.Perm.sign τ : ℤ) : 𝕜) * ((Equiv.Perm.sign τ : ℤ) : 𝕜) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    linear_combination (-(((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, A (τ i) (σ (τ i)))) * hτ
  rw [Finset.sum_congr rfl fun τ _ => key τ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, nsmul_eq_mul]

/-- **The Andréief identity.** Let `m` be a σ-finite measure and let `f i, g j : α → 𝕜` be such
that every product `f i * g j` is `m`-integrable. Then
`det [∫ f i * g j ∂m]_{i,j} = (1 / p!) ∫ det [f i (y k)]_{i,k} * det [g j (y l)]_{j,l} dmᵖ(y)`,
where `p = card ι` and `mᵖ = Measure.pi (fun _ => m)`. -/
@[zeta5irr "lem_real_andreief_general"]
theorem det_integral_mul_eq (m : Measure α) [SigmaFinite m] (f g : ι → α → 𝕜)
    (hfg : ∀ i j, Integrable (fun y => f i y * g j y) m) :
    (Matrix.of fun i j => ∫ y, f i y * g j y ∂m).det =
      ((Fintype.card ι).factorial : 𝕜)⁻¹ *
        ∫ y : ι → α, (Matrix.of fun i k => f i (y k)).det *
          (Matrix.of fun j l => g j (y l)).det ∂(Measure.pi fun _ => m) := by
  have hint : ∫ y : ι → α, (Matrix.of fun i k => f i (y k)).det *
      (Matrix.of fun j l => g j (y l)).det ∂(Measure.pi fun _ => m) =
      ((Fintype.card ι).factorial : 𝕜) *
        (Matrix.of fun i j => ∫ y, f i y * g j y ∂m).det := by
    simp_rw [det_mul_det_eq_sum]
    rw [integral_finsetSum _ fun τ _ => integrable_finsetSum _ fun π _ =>
      (Integrable.fintype_prod (f := fun k y => f (τ k) y * g (π k) y)
        fun k => hfg _ _).const_mul _, ← sum_sum_sign_mul_prod_eq]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [integral_finsetSum _ fun π _ =>
      (Integrable.fintype_prod (f := fun k y => f (τ k) y * g (π k) y)
        fun k => hfg _ _).const_mul _]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [integral_const_mul, integral_fintype_prod_eq_prod (f := fun k y => f (τ k) y * g (π k) y)]
    simp only [of_apply]
  rw [hint, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    one_mul]

end Zeta5Irr
