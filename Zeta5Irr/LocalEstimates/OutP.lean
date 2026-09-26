/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InDtail
public import Zeta5Irr.LocalEstimates.OutQ

/-!
# The complementary class factor `P_a`

For a prime `p` and an integer `a`, the far poles `N < j ≤ K` split according to whether
`j ≡ ±a (mod p)` or not. The complementary class factor is the product over the poles of the
second kind,
`P_a(t) = ∏_{N < j ≤ K, j ≢ ±a (mod p)} (t + j²)`.
Together with the class factor `Q_a`, the product over the poles of the first kind, it
factors the tail polynomial: `Q_a P_a = D_tail`.

## Main definitions

* `Zeta5Irr.complClassFactor`: the polynomial `P_a` over a commutative ring `R`.

## Main results

* `Zeta5Irr.complClassFactor_monic`: `P_a` is monic.
* `Zeta5Irr.natDegree_complClassFactor`: its degree is the number of `N < j ≤ K` with
  `j ≢ ±a (mod p)`.
* `Zeta5Irr.eval_complClassFactor`: `P_a(t) = ∏_{N < j ≤ K, j ≢ ±a} (t + j²)`.
* `Zeta5Irr.eval_neg_sq_complClassFactor`: `P_a(-j²) = 0` for `N < j ≤ K`, `j ≢ ±a (mod p)`.
* `Zeta5Irr.prod_mul_complClassFactor`: `Q_a · P_a = D_tail`.
* `Zeta5Irr.natDegree_complClassFactor_mul_lt`: `deg (P_a Q) < K - N` for `Q` monic of degree
  `< deg Q_a`.
* `Zeta5Irr.complClassFactor_dvd_dTail`: `P_a ∣ D_tail`.

## Implementation notes

* The source uses `N = 3n` and `K = 40n`; here, as for `Zeta5Irr.dTail`, `N` and `K` are
  arbitrary natural numbers, and the definition is made over any commutative ring.
* The congruence `j ≡ ±a (mod p)` is expressed in `ZMod p`, as `(j : ZMod p) = a` or
  `(j : ZMod p) = -a`. Primality of `p` plays no role in the definition and is not assumed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8: the outer range, the separating basis.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable (R : Type*) [CommRing R]

/-- The complementary class factor
`P_a(t) = ∏_{N < j ≤ K, j ≢ ±a (mod p)} (t + j²)` over a commutative ring `R`. -/
@[zeta5irr "def_out_P"]
noncomputable def complClassFactor (p : ℕ) (a : ℤ) (N K : ℕ) : R[X] :=
  ∏ j ∈ (Icc (N + 1) K).filter (fun j : ℕ ↦ ¬((j : ZMod p) = a ∨ (j : ZMod p) = -a)),
    (X + C ((j : R) ^ 2))

variable {R}

/-- The complementary class factor is monic. -/
theorem complClassFactor_monic (p : ℕ) (a : ℤ) (N K : ℕ) :
    (complClassFactor R p a N K).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

/-- The degree of the complementary class factor is the number of `N < j ≤ K` with
`j ≢ ±a (mod p)`. -/
theorem natDegree_complClassFactor [Nontrivial R] (p : ℕ) (a : ℤ) (N K : ℕ) :
    (complClassFactor R p a N K).natDegree =
      #((Icc (N + 1) K).filter (fun j : ℕ ↦ ¬((j : ZMod p) = a ∨ (j : ZMod p) = -a))) := by
  unfold complClassFactor
  rw [natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]

/-- Evaluation of the complementary class factor:
`P_a(t) = ∏_{N < j ≤ K, j ≢ ±a (mod p)} (t + j²)`. -/
theorem eval_complClassFactor (p : ℕ) (a : ℤ) (N K : ℕ) (t : R) :
    (complClassFactor R p a N K).eval t =
      ∏ j ∈ (Icc (N + 1) K).filter (fun j : ℕ ↦ ¬((j : ZMod p) = a ∨ (j : ZMod p) = -a)),
        (t + (j : R) ^ 2) := by
  simp [complClassFactor, eval_prod]

/-- Every far pole outside the class of `±a` is a root: `P_a(-j²) = 0` for `N < j ≤ K` with
`j ≢ ±a (mod p)`. -/
theorem eval_neg_sq_complClassFactor {p : ℕ} {a : ℤ} {N K j : ℕ} (hj : j ∈ Icc (N + 1) K)
    (hja : ¬((j : ZMod p) = a ∨ (j : ZMod p) = -a)) :
    (complClassFactor R p a N K).eval (-(j : R) ^ 2) = 0 := by
  rw [eval_complClassFactor]
  exact prod_eq_zero (mem_filter.2 ⟨hj, hja⟩) (by ring)

/-- The class factor times the complementary class factor is the tail polynomial:
`Q_a · P_a = D_tail`, where `Q_a = ∏_{N < j ≤ K, j ≡ ±a (mod p)} (t + j²)`. -/
theorem prod_mul_complClassFactor (p : ℕ) (a : ℤ) (N K : ℕ) :
    residuePoleProduct R p a N K * complClassFactor R p a N K = dTail R N K := by
  rw [residuePoleProduct, residuePoleIndices, ← Finset.Icc_add_one_left_eq_Ioc]
  exact prod_filter_mul_prod_filter_not _ _ _

/-- If `Q` is monic of degree `< deg Q_a`, then `P_a Q` has degree `< K - N`. -/
theorem natDegree_complClassFactor_mul_lt [Nontrivial R] {p : ℕ} {a : ℤ} {N K : ℕ} {Q : R[X]}
    (hQ : Q.Monic) (hi : Q.natDegree < #(residuePoleIndices p a N K)) :
    (complClassFactor R p a N K * Q).natDegree < K - N := by
  rw [(complClassFactor_monic p _ N K).natDegree_mul hQ, natDegree_complClassFactor]
  have hsum := card_filter_add_card_filter_not (s := Ioc N K)
    (fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a)
  rw [Nat.card_Ioc] at hsum
  rw [residuePoleIndices] at hi
  rw [Finset.Icc_add_one_left_eq_Ioc]
  omega

/-- The complementary class factor divides the tail polynomial. -/
theorem complClassFactor_dvd_dTail (p : ℕ) (a : ℤ) (N K : ℕ) :
    complClassFactor R p a N K ∣ dTail R N K :=
  Dvd.intro_left _ (prod_mul_complClassFactor p a N K)

end Zeta5Irr
