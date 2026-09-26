/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDistAdd
public import Zeta5Irr.LocalFunctional.TauDistCancel
public import Zeta5Irr.LocalFunctional.TauDistDiff
public import Zeta5Irr.LocalFunctional.TauDistPoly
public import Zeta5Irr.LocalFunctional.TauDistRecip
public import Zeta5Irr.LocalFunctional.TauDistReflect
public import Zeta5Irr.LocalFunctional.TauDistSmul
public import Zeta5Irr.LocalFunctional.TauPf
public import Zeta5Irr.LocalFunctional.TauXDecomp

/-!
# Distribution: `τ_X = 𝒯_p`

Let `p ≥ 5` be a prime, `R ⊆ ℤ` finite and `A ∈ ℚ[x]`. Then `τ_X(A; R) = 𝒯_p(A; R)` in
`ℚ_p[X]`: the distributed functional `𝒯_p` built from the local data at `p` recovers the
global functional `τ_X`.

The proof has two steps. First, for a single pole with numerator `1`, the difference
`F(r) = 𝒯_p(1; {r}) - (H_{d(r)}^{(5)} - X)` vanishes at `r = 0`, is invariant under
`r ↦ r - 1` for `r ≠ 0` (both summands change by `-r⁻⁵`), and is invariant under the
reflection `r ↦ -1 - r`; hence `F ≡ 0`. Second, the partial fraction decomposition
`A = P E_R + ∑_{r ∈ R} c_r E_{R \ {r}}` with `c_r = A(r) / E_R'(r)` reduces both functionals,
by linearity and by cancellation of the linear factors `x - r'`, to
`τ(P) + ∑_{r ∈ R} c_r · (value at the single pole r)`.

## Main results

* `Zeta5Irr.tauDist_singleton_one_eq`: `𝒯_p(1; {r}) = H_{d(r)}^{(5)} - X`.
* `Zeta5Irr.tauDist_intPoleProduct_mul`: `𝒯_p(E_T B; T ∪ S) = 𝒯_p(B; S)` for disjoint
  `T`, `S`.
* `Zeta5Irr.map_tauX_eq_tauDist`: `τ_X(A; R) = 𝒯_p(A; R)` in `ℚ_p[X]`.

## Implementation notes

The functional `τ_X(A; R)` lives in `ℚ[X]`; the identity is stated after mapping it to
`ℚ_p[X]` along `ℚ → ℚ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **A single pole.** For a prime `p ≥ 5` and `r ∈ ℤ`,
`𝒯_p(1; {r}) = H_{d(r)}^{(5)} - X` in `ℚ_p[X]`. -/
theorem tauDist_singleton_one_eq (hp5 : 5 ≤ p) (r : ℤ) :
    tauDist p {r} 1 = C ((harmonicFive (reflectIndex r) : ℚ) : ℚ_[p]) - X := by
  set F : ℤ → ℚ_[p][X] := fun r ↦
    tauDist p {r} 1 - (C ((harmonicFive (reflectIndex r) : ℚ) : ℚ_[p]) - X) with hF
  have hstep (r : ℤ) : F (r - 1) = F r := by
    have h1 := tauDist_singleton_sub_one_sub hp5 r
    have h2 := congrArg (fun q : ℚ ↦ C (q : ℚ_[p])) (harmonicFive_reflectIndex_sub_one_sub r)
    simp only [Rat.cast_sub, Rat.cast_neg, Rat.cast_inv, Rat.cast_pow, Rat.cast_intCast,
      C_sub, C_neg] at h2
    simp only [hF]
    linear_combination h1 - h2
  have h0 : F 0 = 0 := by
    simp [hF, tauDist_singleton_zero_one, show reflectIndex 0 = 0 from rfl, harmonicFive]
  have hnat (m : ℕ) : F m = 0 := by
    induction m with
    | zero => simpa using h0
    | succ m ih => rw [← ih, ← hstep]; push_cast; ring_nf
  have hall : F r = 0 := by
    rcases le_or_gt 0 r with hr | hr
    · lift r to ℕ using hr
      exact hnat r
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, r = -1 - m := ⟨(-1 - r).toNat, by omega⟩
      rw [← hnat m, hm]
      simp only [hF, tauDist_singleton_neg_one_sub hp5, reflectIndex_neg_one_sub]
  exact sub_eq_zero.1 hall

/-- **Cancellation of a pole polynomial in `𝒯_p`.** For a prime `p` and disjoint finite
`T, S ⊆ ℤ`, `𝒯_p(E_T B; T ∪ S) = 𝒯_p(B; S)`. -/
theorem tauDist_intPoleProduct_mul {T S : Finset ℤ} (h : Disjoint T S) (B : ℚ[X]) :
    tauDist p (T ∪ S) (intPoleProduct T ℚ * B) = tauDist p S B := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert t T ht ih =>
    rw [Finset.disjoint_insert_left] at h
    rw [intPoleProduct_insert ℚ ht, mul_assoc,
      tauDist_X_sub_C_mul (Finset.mem_union_left _ (Finset.mem_insert_self t T)),
      Finset.insert_union, Finset.erase_insert (fun h' ↦ (Finset.mem_union.1 h').elim ht h.1),
      ih h.2]

/-- **Distribution.** For a prime `p ≥ 5`, a finite `R ⊆ ℤ` and `A ∈ ℚ[x]`,
`τ_X(A; R) = 𝒯_p(A; R)` as an identity in `ℚ_p[X]`. -/
@[zeta5irr "lem_distribution"]
theorem map_tauX_eq_tauDist (hp5 : 5 ≤ p) (R : Finset ℤ) (A : ℚ[X]) :
    (tauX R A).map (algebraMap ℚ ℚ_[p]) = tauDist p R A := by
  classical
  set P := A /ₘ intPoleProduct R ℚ
  set c : ℤ → ℚ := fun r ↦
    A.eval (r : ℚ) / (derivative (intPoleProduct R ℚ)).eval (r : ℚ)
  have hdec : A = P * intPoleProduct R ℚ +
      ∑ r ∈ R, C (c r) * intPoleProduct (R.erase r) ℚ := by
    have hB := degree_modByMonic_lt A (monic_intPoleProduct R ℚ)
    rw [degree_intPoleProduct] at hB
    exact eq_mul_prod_add_sum_eval_div_derivative (s := R) (v := fun r : ℤ ↦ (r : ℚ))
      (fun x _ y _ h ↦ Int.cast_injective h)
      (by rw [mul_comm, add_comm]; exact (modByMonic_add_div A _).symm) hB
  let L : ℚ[X] →+ ℚ_[p][X] :=
    { toFun := tauDist p R
      map_zero' := by simpa using tauDist_smul (p := p) R 0 0
      map_add' := tauDist_add R }
  have hL (B : ℚ[X]) : L B = tauDist p R B := rfl
  rw [tauX_eq_of_eq_mul_add_sum c hdec, ← hL, hdec, map_add, map_sum]
  simp only [hL, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, map_C,
    Polynomial.map_sub, map_X]
  congr 1
  · have h := tauDist_intPoleProduct_mul (p := p) (Finset.disjoint_empty_right R) P
    rw [Finset.union_empty] at h
    rw [mul_comm, h, tauDist_empty_eq_tau]
    rfl
  · refine Finset.sum_congr rfl fun r hr ↦ ?_
    have hR : R = R.erase r ∪ {r} := by
      rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hr]
    have h := tauDist_intPoleProduct_mul (p := p)
      (Finset.disjoint_singleton_right.2 (Finset.notMem_erase r R)) 1
    rw [← hR, mul_one] at h
    rw [← smul_eq_C_mul (c r), tauDist_smul, h, tauDist_singleton_one_eq hp5,
      Algebra.smul_def, Polynomial.algebraMap_apply]
    rfl

end Zeta5Irr
