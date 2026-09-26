/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.EllA
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
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
# The residue-class pole products `Q_a`

For a prime `p`, an integer `a` and natural numbers `N ≤ K`, the residue-class pole product is
`Q_a(t) = ∏_{N < j ≤ K, j ≡ ±a (mod p)} (t + j²)`,
the part of the tail polynomial `∏_{j=N+1}^{K} (t + j²)` whose roots `-j²` come from the far
poles `j` lying in the residue classes `±a` modulo `p`. It is a monic polynomial with integer
coefficients, and it depends on `a` only through the pair of classes `±a`; these products are
the building blocks of the separating basis of the outer range.

## Main definitions

* `Zeta5Irr.residuePoleIndices`: the finite set of `N < j ≤ K` with `j ≡ ±a (mod p)`.
* `Zeta5Irr.residuePoleProduct`: the polynomial `∏_{N < j ≤ K, j ≡ ±a (mod p)} (X + j²)` over a
  commutative ring `R`.

## Main results

* `Zeta5Irr.card_residuePoleIndices_add_ellA`: `#{N < j ≤ K : j ≡ ±a} + ℓ_N(a) = ℓ_K(a)`.
* `Zeta5Irr.residuePoleProduct_monic`: `Q_a` is monic.
* `Zeta5Irr.natDegree_residuePoleProduct`: the degree of `Q_a` is the number of `N < j ≤ K`
  with `j ≡ ±a (mod p)` (over a nontrivial ring).
* `Zeta5Irr.eval_residuePoleProduct`: `Q_a(t) = ∏_{N < j ≤ K, j ≡ ±a (mod p)} (t + j²)`.
* `Zeta5Irr.map_residuePoleProduct`: `Q_a` is the image of the integer polynomial `Q_a` under
  any ring homomorphism.
* `Zeta5Irr.residuePoleProduct_neg`, `Zeta5Irr.residuePoleProduct_congr`: `Q_{-a} = Q_a`, and
  `Q_a` depends only on the class of `a` modulo `p`.
* `Zeta5Irr.residuePoleProduct_dvd`: `Q_a` divides `∏_{j=N+1}^{K} (X + j²)`.

## Implementation notes

* The source fixes `N = 3n` and `K = 40n`; here `N` and `K` are arbitrary natural numbers,
  since the definition and its elementary properties do not depend on them. When `K ≤ N` the
  product is empty and `Q_a = 1`.
* The source needs `p` prime only for the arithmetic its consumers do with `Q_a`; the definition
  is made for any modulus `p : ℕ`, the congruence `j ≡ ±a (mod p)` being read in `ZMod p`.
* The source works with integer coefficients (and over `ℚ` and `ℤ_p`); the definition is made
  over any commutative ring `R`, and `map_residuePoleProduct` identifies each instance with the
  image of the one over `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- The indices `N < j ≤ K` with `j ≡ ±a (mod p)`: the far poles in the residue classes `±a`
modulo `p`. -/
def residuePoleIndices (p : ℕ) (a : ℤ) (N K : ℕ) : Finset ℕ :=
  (Ioc N K).filter fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a

/-- Membership in `residuePoleIndices p a N K`: `N < j ≤ K` and `j ≡ ±a (mod p)`. -/
theorem mem_residuePoleIndices {p : ℕ} {a : ℤ} {N K j : ℕ} :
    j ∈ residuePoleIndices p a N K ↔
      (N < j ∧ j ≤ K) ∧ ((j : ZMod p) = a ∨ (j : ZMod p) = -a) := by
  simp [residuePoleIndices]

/-- The residue-class pole indices are contained in `(N, K]`. -/
theorem residuePoleIndices_subset_Ioc (p : ℕ) (a : ℤ) (N K : ℕ) :
    residuePoleIndices p a N K ⊆ Ioc N K :=
  filter_subset _ _

/-- The pole indices of the classes `±a` and `±(-a)` coincide. -/
@[simp]
theorem residuePoleIndices_neg (p : ℕ) (a : ℤ) (N K : ℕ) :
    residuePoleIndices p (-a) N K = residuePoleIndices p a N K := by
  ext j
  simp only [mem_residuePoleIndices, Int.cast_neg, neg_neg]
  tauto

/-- The far poles `N < j ≤ K` with `j ≡ ±a (mod p)` and the poles `1 ≤ j ≤ N` with
`j ≡ ±a (mod p)` together make up the poles counted by `ℓ_K(a)`: `#{…} + ℓ_N(a) = ℓ_K(a)`. -/
theorem card_residuePoleIndices_add_ellA (p : ℕ) (a : ℤ) {N K : ℕ} (h : N ≤ K) :
    #(residuePoleIndices p a N K) + ellA p N a = ellA p K a := by
  have hU : Icc (1 : ℤ) K = Icc (1 : ℤ) N ∪ Ioc (N : ℤ) K := by
    ext j; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hD : Disjoint (Icc (1 : ℤ) N) (Ioc (N : ℤ) K) := by
    rw [disjoint_left]; intro j h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [ellA, ellA, hU, filter_union, card_union_of_disjoint (disjoint_filter_filter hD),
    add_comm, residuePoleIndices, ← card_filter_Ioc_intCast]

variable (R : Type*) [CommRing R]

/-- The residue-class pole product `Q_a(t) = ∏_{N < j ≤ K, j ≡ ±a (mod p)} (t + j²)` over a
commutative ring `R`. -/
@[zeta5irr "def_out_Q"]
noncomputable def residuePoleProduct (p : ℕ) (a : ℤ) (N K : ℕ) : R[X] :=
  ∏ j ∈ residuePoleIndices p a N K, (X + C ((j : R) ^ 2))

variable {R}

/-- The residue-class pole product is monic. -/
theorem residuePoleProduct_monic (p : ℕ) (a : ℤ) (N K : ℕ) :
    (residuePoleProduct R p a N K).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- The degree of `Q_a` is the number of far poles `N < j ≤ K` with `j ≡ ±a (mod p)`. -/
theorem natDegree_residuePoleProduct [Nontrivial R] (p : ℕ) (a : ℤ) (N K : ℕ) :
    (residuePoleProduct R p a N K).natDegree = #(residuePoleIndices p a N K) := by
  rw [residuePoleProduct, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]

/-- Evaluation of the residue-class pole product:
`Q_a(t) = ∏_{N < j ≤ K, j ≡ ±a (mod p)} (t + j²)`. -/
theorem eval_residuePoleProduct (p : ℕ) (a : ℤ) (N K : ℕ) (t : R) :
    (residuePoleProduct R p a N K).eval t =
      ∏ j ∈ residuePoleIndices p a N K, (t + (j : R) ^ 2) := by
  simp [residuePoleProduct, eval_prod]

/-- The residue-class pole product commutes with ring homomorphisms. -/
theorem map_residuePoleProduct {S : Type*} [CommRing S] (f : R →+* S) (p : ℕ) (a : ℤ)
    (N K : ℕ) : (residuePoleProduct R p a N K).map f = residuePoleProduct S p a N K := by
  simp [residuePoleProduct, Polynomial.map_prod]

/-- Over any commutative ring, `Q_a` is the image of the integer polynomial `Q_a`. -/
theorem map_intCast_residuePoleProduct (p : ℕ) (a : ℤ) (N K : ℕ) :
    (residuePoleProduct ℤ p a N K).map (Int.castRingHom R) = residuePoleProduct R p a N K :=
  map_residuePoleProduct _ p a N K

/-- `Q_a` depends on `a` only through the pair of classes `±a`: `Q_{-a} = Q_a`. -/
@[simp]
theorem residuePoleProduct_neg (p : ℕ) (a : ℤ) (N K : ℕ) :
    residuePoleProduct R p (-a) N K = residuePoleProduct R p a N K := by
  rw [residuePoleProduct, residuePoleProduct, residuePoleIndices_neg]

/-- `Q_a` depends on `a` only through its residue class modulo `p`. -/
theorem residuePoleProduct_congr (p : ℕ) {a b : ℤ} (h : (a : ZMod p) = b) (N K : ℕ) :
    residuePoleProduct R p a N K = residuePoleProduct R p b N K := by
  simp only [residuePoleProduct, residuePoleIndices, h]

/-- The residue-class pole product is `1` when `K ≤ N`. -/
theorem residuePoleProduct_of_le {p : ℕ} {a : ℤ} {N K : ℕ} (h : K ≤ N) :
    residuePoleProduct R p a N K = 1 := by
  rw [residuePoleProduct, residuePoleIndices, Ioc_eq_empty (by omega), filter_empty, prod_empty]

/-- `Q_a` divides the tail polynomial `∏_{j=N+1}^{K} (X + j²)`. -/
theorem residuePoleProduct_dvd (p : ℕ) (a : ℤ) (N K : ℕ) :
    residuePoleProduct R p a N K ∣ ∏ j ∈ Ioc N K, (X + C ((j : R) ^ 2)) :=
  prod_dvd_prod_of_subset _ _ (fun j : ℕ ↦ X + C ((j : R) ^ 2))
    (residuePoleIndices_subset_Ioc p a N K)

end Zeta5Irr
