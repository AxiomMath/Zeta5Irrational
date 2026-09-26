/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The pole product of an initial segment

For `m ≥ 0`, `D_m` denotes the pole product `D_S` for the initial segment
`S = {1, 2, …, m}` of the positive integers, that is
`D_m(t) = ∏_{j = 1}^{m} (t + j ^ 2)`. In particular `D_0 = 1`, and
`D_{m + 1} = D_m · (t + (m + 1) ^ 2)`. It is monic of degree `m`, and `D_m`
divides `D_n` whenever `m ≤ n`.

## Main definitions

* `Zeta5Irr.poleProductRange`: the polynomial `D_m = D_{{1, …, m}}`.

## Main results

* `Zeta5Irr.poleProductRange_zero`: `D_0 = 1`.
* `Zeta5Irr.poleProductRange_succ`: `D_{m + 1} = D_m · (t + (m + 1) ^ 2)`.
* `Zeta5Irr.monic_poleProductRange`, `Zeta5Irr.natDegree_poleProductRange`,
  `Zeta5Irr.degree_poleProductRange`: `D_m` is monic of degree `m`.
* `Zeta5Irr.poleProductRange_dvd`: `D_m ∣ D_n` for `m ≤ n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and
  the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- `D_m`, the pole product `D_S` of the initial segment `S = {1, 2, …, m}`:
`D_m(t) = ∏_{j = 1}^{m} (t + j ^ 2)`. -/
@[zeta5irr "not_Dm"]
noncomputable def poleProductRange (m : ℕ) (R : Type*) [CommSemiring R] : R[X] :=
  poleProduct (Icc 1 m) R

variable (m : ℕ) (R : Type*) [CommSemiring R]

/-- `D_0 = 1`. -/
@[zeta5irr "not_Dm", simp]
theorem poleProductRange_zero : poleProductRange 0 R = 1 := by
  simp [poleProductRange]

/-- The recursion `D_{m + 1} = D_m · (t + (m + 1) ^ 2)`. -/
theorem poleProductRange_succ :
    poleProductRange (m + 1) R = poleProductRange m R * (X + C (((m + 1 : ℕ) : R) ^ 2)) := by
  rw [poleProductRange, poleProductRange, ← insert_Icc_right_eq_Icc_add_one (Nat.le_add_left 1 m),
    poleProduct_insert _ (by simp), mul_comm]

/-- `D_m` as a product over `range m`: `D_m = ∏_{i < m} (t + (i + 1) ^ 2)`. -/
theorem poleProductRange_eq_prod_range :
    poleProductRange m R = ∏ i ∈ range m, (X + C (((i + 1 : ℕ) : R) ^ 2)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [poleProductRange_succ, ih, prod_range_succ]

/-- `D_1 = t + 1`. -/
@[simp]
theorem poleProductRange_one : poleProductRange 1 R = X + 1 := by
  simp [poleProductRange_eq_prod_range]

/-- `D_m` is monic. -/
theorem monic_poleProductRange : (poleProductRange m R).Monic :=
  monic_poleProduct _ R

/-- `D_m ≠ 0` over a nontrivial semiring. -/
theorem poleProductRange_ne_zero [Nontrivial R] : poleProductRange m R ≠ 0 :=
  poleProduct_ne_zero _ R

/-- `D_m` has degree `m`. -/
@[simp]
theorem natDegree_poleProductRange [Nontrivial R] : (poleProductRange m R).natDegree = m := by
  simp [poleProductRange]

/-- `D_m` has degree `m`, stated with `Polynomial.degree`. -/
theorem degree_poleProductRange [Nontrivial R] : (poleProductRange m R).degree = m := by
  rw [poleProductRange, degree_poleProduct, Nat.card_Icc, Nat.add_sub_cancel]

/-- The value of `D_m` at `t` is `∏_{j = 1}^{m} (t + j ^ 2)`. -/
@[simp]
theorem eval_poleProductRange (t : R) :
    (poleProductRange m R).eval t = ∏ j ∈ Icc 1 m, (t + (j : R) ^ 2) :=
  eval_poleProduct _ R t

/-- `D_m` is compatible with base change along a ring homomorphism. -/
@[simp]
theorem map_poleProductRange {R' : Type*} [CommSemiring R'] (f : R →+* R') :
    (poleProductRange m R).map f = poleProductRange m R' :=
  map_poleProduct _ R f

/-- `D_m ∣ D_n` whenever `m ≤ n`. -/
theorem poleProductRange_dvd {m n : ℕ} (h : m ≤ n) :
    poleProductRange m R ∣ poleProductRange n R := by
  rw [poleProductRange, poleProductRange, poleProduct, poleProduct]
  exact prod_dvd_prod_of_subset _ _ _ (Icc_subset_Icc_right h)

end Zeta5Irr
