/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.FKBasis
public import Zeta5Irr.LocalFunctional.Pullback
public import Zeta5Irr.LocalFunctional.SmallPrime
public import Zeta5Irr.LocalFunctional.LocalVpGDet
public import Zeta5Irr.LocalFunctional.FiIntvalued

/-!
# The Gauss valuation of `F_K`

For every prime `p`,
`v_p^G(F_K) ≥ -6 h ⌊log_p (5K)⌋ - h v_p(24)`.

By the pullback formula, `(K!)² μ_X(A; {1, …, K}) = (-1)^K τ_X((K!)² x⁵ A(-x²); R_K)`, so the
small-prime bound applies to every entry `(K!)² μ_X(f_i f_j; {1, …, K})` of the matrix whose
determinant is `F_K`. The degree of `x⁵ f_i(-x²) f_j(-x²)` is at most `12N + 4h + 1`, and
`max(2K, 12N + 4h + 2) ≤ 5K`, so every entry has Gauss valuation at least
`-6 ⌊log_p (5K)⌋ - v_p(24)`; the determinant bound then gives the claim.

## Main results

* `Zeta5Irr.le_vpG_factorial_sq_mul_rationalFunctional`: the entry bound for a general
  numerator `A ∈ ℚ[t]` taking integer values at the points `-m²`.
* `Zeta5Irr.le_vpG_normalizedDet`: the bound `v_p^G(F_K) ≥ -6h ⌊log_p(5K)⌋ - h v_p(24)`.

## Implementation notes

* `F_K ∈ ℚ[X]` is taken in `ℚ_p[X]` by mapping its coefficients along `ℚ → ℚ_p`.
* `⌊log_p n⌋` is `Nat.log p n` and `v_p(24)` is `padicValNat p 24`.
* The bound holds for `n = 0` as well (then `h = 0` and `F_K` is the empty determinant), so the
  standing hypothesis `n ≥ 1` is not assumed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.7 (The integer-valued basis).
-/

@[expose] public section

open Polynomial Finset
open scoped Nat

namespace Zeta5Irr

variable {p : ℕ} [Fact p.Prime]

/-- `R_K = {1, …, K} ∪ {-1, …, -K}`. -/
theorem puncturedIcc_eq_image_union_image_neg (K : ℕ) :
    puncturedIcc K =
      (Icc 1 K).image (fun j : ℕ ↦ (j : ℤ)) ∪ (Icc 1 K).image (fun j : ℕ ↦ -(j : ℤ)) := by
  ext s
  simp only [mem_puncturedIcc, mem_union, mem_image, mem_Icc]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rcases lt_or_gt_of_ne h0 with h | h
    · exact Or.inr ⟨s.natAbs, by omega, by omega⟩
    · exact Or.inl ⟨s.natAbs, by omega, by omega⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega

/-- Let `A ∈ ℚ[t]` take integer values at the points `-m²`, `m ∈ ℤ`, and have degree at most
`e`. Then `v_p^G((K!)² μ_X(A; {1, …, K})) ≥ -6 ⌊log_p max(2K, 2e + 6)⌋ - v_p(24)`. -/
theorem le_vpG_factorial_sq_mul_rationalFunctional {K e : ℕ} {A : ℚ[X]}
    (hA : ∀ m : ℤ, ∃ z : ℤ, A.eval (-(m : ℚ) ^ 2) = z) (hAe : A.natDegree ≤ e) :
    ((-6 * Nat.log p (max (2 * K) (2 * e + 6)) - padicValNat p 24 : ℤ) : WithTop ℤ) ≤
      vpG ((C ((K ! : ℚ) ^ 2) * rationalFunctional (Icc 1 K) A).map (algebraMap ℚ ℚ_[p])) := by
  set B : ℚ[X] := X ^ 5 * A.comp (-X ^ 2) with hB
  have hcard : #(Icc 1 K) = K := by simp
  have hpull : C ((K ! : ℚ) ^ 2) * rationalFunctional (Icc 1 K) A =
      C ((-1 : ℚ) ^ K) * tauX (puncturedIcc K) (C ((K ! : ℚ) ^ 2) * B) := by
    rw [rationalFunctional_eq_tauX (by simp), hcard, ← puncturedIcc_eq_image_union_image_neg,
      mul_assoc, ← smul_eq_C_mul (p := B) ((-1 : ℚ) ^ K), tauX_smul,
      ← smul_eq_C_mul (p := B) ((K ! : ℚ) ^ 2), tauX_smul, smul_eq_C_mul, smul_eq_C_mul]
    ring
  have hBint : ∀ m : ℤ, ∃ n : ℤ, B.eval (m : ℚ) = n := fun m ↦ by
    obtain ⟨z, hz⟩ := hA m
    refine ⟨m ^ 5 * z, ?_⟩
    simp only [hB, eval_mul, eval_pow, eval_X, eval_comp, eval_neg]
    rw [hz]
    push_cast
    ring
  have hBd : B.natDegree ≤ 2 * e + 5 := by
    rw [hB]
    have h1 : (A.comp (-X ^ 2)).natDegree ≤ A.natDegree * 2 :=
      natDegree_comp_le.trans (by rw [natDegree_neg, natDegree_X_pow])
    have h2 := natDegree_mul_le (p := (X : ℚ[X]) ^ 5) (q := A.comp (-X ^ 2))
    rw [natDegree_X_pow] at h2
    omega
  have hlog : Nat.log p (max (2 * K) (2 * e + 5 + 1)) = Nat.log p (max (2 * K) (2 * e + 6)) :=
    rfl
  have key := le_vpG_tauX_factorial_sq_mul (p := p) (K := K) hBint hBd
  rw [hlog] at key
  rw [hpull, Polynomial.map_mul, vpG, map_C, gaussAddVal_C_mul, map_pow, map_neg, map_one]
  rcases neg_one_pow_eq_or ℚ_[p] K with h | h <;> rw [h] <;> simpa using key

/-- **Gauss valuation of `F_K`.** For every prime `p`,
`v_p^G(F_K) ≥ -6 h ⌊log_p (5K)⌋ - h v_p(24)`, where `K = 40 n` and `h = 37 n`. -/
@[zeta5irr "prop_vpG_FK"]
theorem le_vpG_normalizedDet (n : ℕ) :
    ((-6 * matrixOrder n * Nat.log p (5 * poleBound n) - matrixOrder n * padicValNat p 24 : ℤ) :
        WithTop ℤ) ≤ vpG ((normalizedDet n).map (algebraMap ℚ ℚ_[p])) := by
  set c : ℤ := -6 * Nat.log p (5 * poleBound n) - padicValNat p 24
  rw [normalizedDet_eq_det_rationalFunctional_poleWeightedBasis, ← coe_mapRingHom,
    RingHom.map_det]
  have key := card_mul_le_vpG_det (RingHom.mapMatrix (mapRingHom (algebraMap ℚ ℚ_[p]))
    (Matrix.of fun i j : Fin (matrixOrder n) =>
      C (((poleBound n).factorial : ℚ) ^ 2) *
        rationalFunctional (Icc 1 (poleBound n))
          (poleWeightedBasis (innerDegree n) i * poleWeightedBasis (innerDegree n) j))) c
    (fun i j ↦ by
      have hi := i.isLt
      have hj := j.isLt
      set e := 6 * innerDegree n + 2 * matrixOrder n - 2
      have hA : ∀ m : ℤ, ∃ z : ℤ, (poleWeightedBasis (innerDegree n) i *
          poleWeightedBasis (innerDegree n) j).eval (-(m : ℚ) ^ 2) = z := fun m ↦ by
        obtain ⟨a, ha⟩ := exists_eval_poleWeightedBasis_neg_sq_eq_intCast (innerDegree n) i m
        obtain ⟨b, hb⟩ := exists_eval_poleWeightedBasis_neg_sq_eq_intCast (innerDegree n) j m
        exact ⟨a * b, by rw [eval_mul, ha, hb]; push_cast; rfl⟩
      have hAe : (poleWeightedBasis (innerDegree n) i *
          poleWeightedBasis (innerDegree n) j).natDegree ≤ e := by
        refine natDegree_mul_le.trans ?_
        rw [natDegree_poleWeightedBasis, natDegree_poleWeightedBasis]
        omega
      have hlog : Nat.log p (max (2 * poleBound n) (2 * e + 6)) ≤
          Nat.log p (5 * poleBound n) := by
        refine Nat.log_mono_right (max_le ?_ ?_)
        · omega
        · simp only [e, innerDegree, matrixOrder, poleBound] at hi ⊢
          omega
      refine le_trans ?_ (le_vpG_factorial_sq_mul_rationalFunctional hA hAe)
      simp only [c]
      exact_mod_cast (by omega :
        -6 * (Nat.log p (5 * poleBound n) : ℤ) - padicValNat p 24 ≤
          -6 * (Nat.log p (max (2 * poleBound n) (2 * e + 6)) : ℤ) - padicValNat p 24))
  refine le_trans (le_of_eq ?_) key
  simp only [c, Fintype.card_fin]
  congr 1
  ring

end Zeta5Irr
