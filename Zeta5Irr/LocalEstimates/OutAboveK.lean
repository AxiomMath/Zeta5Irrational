/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InBasisChange
public import Zeta5Irr.LocalEstimates.OutBasisChange
public import Zeta5Irr.LocalEstimates.OutEntryInt
public import Zeta5Irr.LocalEstimates.OutLInt

/-!
# Primes above `K` do not divide `Δ_K`

Let `K = 40 n` with `n > 0` and let `p` be a prime with `p > K`. Then `v_p^G(Δ_K) ≥ 0`.

Put `N = 3 n`, `h = 37 n` and `S = {N + 1, …, K}`. Since `p > K ≥ 40`, `p` is odd and `p ≥ 7`,
and every `1 ≤ j ≤ K` satisfies `j < p`. For `0 ≤ a ≤ m°` let `Q_a` and `P_a` be the class
factor and the complementary class factor, so that `Q_a P_a = D_tail = D_S`, and consider the
polynomials `P_a (t + a²)^i` for `0 ≤ i < deg Q_a`. The factors `Q_a` are monic, multiply to
`D_tail` and are pairwise coprime modulo `p`, so by the distributing basis lemma these
polynomials form a `ℤ_p`-basis of the polynomials of degree `< h`; their coefficient matrix `C`
is square with `det C ∈ ℤ_p^×`, and `B = C G_K Cᵀ` has `v_p^G(det B) = v_p^G(Δ_K)`.

By bilinearity, `B_{(a,i),(c,j)} = Φ(P_a (t + a²)^i, P_c (t + c²)^j)`. The quotient of the
numerator `D_N⁵ P_a (t + a²)^i P_c (t + c²)^j` by `D_S` has degree at most `52 n - 2 < 2p - 3`,
so the moment part of `Φ` only sees the moments `μ(t^e)` with `e < 2p - 3`, which are `p`-adic
integers: the entry equals its integral part `μ_{0,X}`. If `a ≠ c`, every residue vanishes. If
`a = c`, the residues come from the poles `j ∈ S` in the class `±a`, which lie among `a` and
`p - a`: a single such pole contributes an integer multiple of `ν_j(X) ∈ ℤ_p[X]`, and a pair
`{a, p - a}` contributes a divided difference `(u₁ ν_a(X) - u₂ ν_{p-a}(X)) / (p (p - 2a))` with
`u₁ ≡ u₂ (mod p)`, which lies in `ℤ_p[X]`. So every entry of `B` lies in `ℤ_p[X]`, hence so does
`det B`, and `v_p^G(Δ_K) = v_p^G(det B) ≥ 0`.

## Main definitions

* `Zeta5Irr.classPowCoeffMatrix`: the matrix `C` whose row `(a, i)` is the coefficient vector
  of `P_a (t + a²)^i`.

## Main results

* `Zeta5Irr.map_rationalFunctional_eq_truncatedPoleFunctional`: `μ_X(A; S) = μ_{0,X}(A; S)`
  when the quotient of `A` by `D_S` has degree `< 2p - 3`.
* `Zeta5Irr.isUnit_det_classPowCoeffMatrix`: `det C ∈ ℤ_p^×`.
* `Zeta5Irr.truncatedPoleFunctional_complClassFactor_mul_mem_lifts`: for `K < p`,
  `μ_{0,X}(D_N⁵ (P_a f)(P_a g); S) ∈ ℤ_p[X]` for all `f, g ∈ ℤ[t]`.
* `Zeta5Irr.zero_le_vpG_gramDet_of_poleBound_lt`: `v_p^G(Δ_K) ≥ 0` for every prime `p > K`.

## Implementation notes

* The rows of `C` are indexed by the pairs `(a, i)` with `0 ≤ a ≤ m°` and `i < deg Q_a`, as for
  the outer coefficient matrix `C^out`; the class `a = 0` contributes no rows when `p > K`. The
  polynomials `(t + a²)^i` replace the local polynomials `q_{a,i}` of `C^out`, whose degrees
  are only controlled when `p ≤ K`.
* Instead of the determinant bound with weights `0`, the conclusion `v_p^G(det B) ≥ 0` is drawn
  from `det B ∈ ℤ_p[X]`, which holds because `ℤ_p[X]` is a subring of `ℚ_p[X]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.12 (The outer range: the conjugated decomposition).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- If the quotient of `A` by `D_S` has degree `< 2p - 3`, the rational functional and its
integral part agree: `μ_X(A; S) = μ_{0,X}(A; S)` in `ℚ_p[X]`. -/
theorem map_rationalFunctional_eq_truncatedPoleFunctional {S : Finset ℕ} {A : ℚ[X]}
    (hA : (A /ₘ poleProduct S ℚ).natDegree < 2 * p - 3) :
    (rationalFunctional S A).map (algebraMap ℚ ℚ_[p]) = truncatedPoleFunctional p S A := by
  rw [← sub_eq_zero, map_rationalFunctional_sub_truncatedPoleFunctional,
    momentFunctional_sub_truncatedMomentFunctional, C_eq_zero]
  refine sum_eq_zero fun e he ↦ ?_
  rw [mem_filter, mem_support_iff] at he
  exact absurd (le_natDegree_of_ne_zero he.1) (by omega)

/-- For odd `p`, `0 ≤ a ≤ m°` and `j < p`, if `j ≡ ±a (mod p)` then `j = a` or `j = p - a`. -/
theorem eq_or_eq_sub_of_natCast_eq_or_eq_neg {q : ℕ} (hq : Odd q) {a j : ℕ} (ha : a ≤ mStar q)
    (hj : j < q)
    (h : (j : ZMod q) = ((a : ℤ) : ZMod q) ∨ (j : ZMod q) = -((a : ℤ) : ZMod q)) :
    j = a ∨ j = q - a := by
  have := (natCast_eq_or_eq_neg_iff hq ha j).1 h
  rw [Nat.mod_eq_of_lt hj] at this
  split_ifs at this <;> omega

/-- For a prime `p ≥ 7` with `K < p` and `0 ≤ a ≤ m°`, the integral part
`μ_{0,X}(D_N⁵ (P_a f)(P_a g); {N + 1, …, K})` lies in `ℤ_p[X]` for all `f, g ∈ ℤ[t]`. -/
theorem truncatedPoleFunctional_complClassFactor_mul_mem_lifts (hp7 : 7 ≤ p) {N K : ℕ}
    (hKp : K < p) {a : ℕ} (ha : a ≤ mStar p) (f g : ℤ[X]) :
    truncatedPoleFunctional p (Icc (N + 1) K)
        ((poleProductRange N ℤ ^ 5 * (complClassFactor ℤ p (a : ℤ) N K * f) *
          (complClassFactor ℤ p (a : ℤ) N K * g)).map (Int.castRingHom ℚ)) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h2a : 2 * a < p := by have := two_mul_mStar_add_one hodd; omega
  set T := residuePoleIndices p (a : ℤ) N K with hTdef
  have hTS : T ⊆ Icc (N + 1) K := by
    rw [Finset.Icc_add_one_left_eq_Ioc]; exact residuePoleIndices_subset_Ioc _ _ _ _
  have hTmem : ∀ k ∈ T, k = a ∨ k = p - a := fun k hk ↦ by
    rw [hTdef, mem_residuePoleIndices] at hk
    exact eq_or_eq_sub_of_natCast_eq_or_eq_neg hodd ha (by omega) hk.2
  have hTlt : ∀ k ∈ T, k < p := fun k hk ↦ by
    rw [hTdef, mem_residuePoleIndices] at hk; omega
  let Bz : ℤ[X] := poleProductRange N ℤ ^ 5 * complClassFactor ℤ p (a : ℤ) N K * f * g
  have hD : poleProduct (Icc (N + 1) K) ℚ =
      poleProduct T ℚ * complClassFactor ℚ p (a : ℤ) N K := by
    exact (prod_mul_complClassFactor p (a : ℤ) N K).symm
  have hA : (poleProductRange N ℤ ^ 5 * (complClassFactor ℤ p (a : ℤ) N K * f) *
      (complClassFactor ℤ p (a : ℤ) N K * g)).map (Int.castRingHom ℚ) =
      Bz.map (Int.castRingHom ℚ) * complClassFactor ℚ p (a : ℤ) N K := by
    simp only [Bz, Polynomial.map_mul, Polynomial.map_pow, map_poleProductRange,
      map_complClassFactor]
    ring
  rw [truncatedPoleFunctional_eq_of_poleProduct_eq_mul hTS hD hA]
  refine add_mem ?_ ?_
  · rw [← map_poleProduct _ ℤ (Int.castRingHom ℚ), ← map_divByMonic _ (monic_poleProduct _ ℤ)]
    exact C_mem_lifts (PadicInt.Coe.ringHom (p := p))
      ⟨_, norm_truncatedMomentFunctional_map_intCast_le_one hp7 _⟩
  by_cases hpair : a ∈ T ∧ p - a ∈ T
  · -- two poles `a` and `p - a` in the class: a divided difference
    have ha1 : 1 ≤ a := by
      have := hpair.2; rw [hTdef, mem_residuePoleIndices] at this; omega
    have hT2 : T = {a, p - a} := by
      ext k
      rw [mem_insert, mem_singleton]
      refine ⟨hTmem k, ?_⟩
      rintro (rfl | rfl)
      exacts [hpair.1, hpair.2]
    rw [hT2]
    exact sum_pair_div_smul_poleValue_mem_lifts hp2 ha1 h2a Bz
  · -- at most one pole in the class: an integer multiple of `ν_j(X)`
    refine sum_mem fun k hk ↦ ?_
    have hek : T.erase k = ∅ := by
      refine eq_empty_of_forall_notMem fun k' hk' ↦ hpair ?_
      rw [mem_erase] at hk'
      rcases hTmem k hk with rfl | rfl <;> rcases hTmem k' hk'.2 with rfl | rfl
      exacts [absurd rfl hk'.1, ⟨hk, hk'.2⟩, ⟨hk'.2, hk⟩, absurd rfl hk'.1]
    rw [hek, poleProduct_empty, eval_one, div_one]
    exact eval_smul_poleValue_mem_lifts hp2 (hTlt k hk) Bz

section Matrix

variable (R : Type*) [CommRing R]

/-- The coefficient matrix of the polynomials `P_a (t + a²)^i`: rows are indexed by the pairs
`(a, i)` with `0 ≤ a ≤ m°` and `0 ≤ i < deg Q_a`, columns by `0 ≤ k < h`, and the entry at
`((a, i), k)` is the coefficient of `t^k` in `P_a (t + a²)^i`. -/
noncomputable def classPowCoeffMatrix (q N K h : ℕ) :
    Matrix (Σ a : Fin (mStar q + 1), Fin #(residuePoleIndices q (a : ℕ) N K)) (Fin h) R :=
  Matrix.of fun ai k ↦
    (complClassFactor R q (ai.1 : ℕ) N K * (X + C (((ai.1 : ℕ) : R) ^ 2)) ^ (ai.2 : ℕ)).coeff k

variable {R}

/-- The entry of `classPowCoeffMatrix` at `((a, i), k)` is the coefficient of `t^k` in
`P_a (t + a²)^i`. -/
theorem classPowCoeffMatrix_apply (q N K h : ℕ)
    (ai : Σ a : Fin (mStar q + 1), Fin #(residuePoleIndices q (a : ℕ) N K)) (k : Fin h) :
    classPowCoeffMatrix R q N K h ai k =
      (complClassFactor R q (ai.1 : ℕ) N K * (X + C (((ai.1 : ℕ) : R) ^ 2)) ^ (ai.2 : ℕ)).coeff
        k :=
  rfl

/-- `classPowCoeffMatrix` commutes with ring homomorphisms. -/
theorem map_classPowCoeffMatrix {S : Type*} [CommRing S] (f : R →+* S) (q N K h : ℕ) :
    (classPowCoeffMatrix R q N K h).map f = classPowCoeffMatrix S q N K h := by
  ext ai k
  rw [Matrix.map_apply, classPowCoeffMatrix_apply, classPowCoeffMatrix_apply, ← coeff_map,
    Polynomial.map_mul, map_complClassFactor]
  simp

/-- For `i < deg Q_a`, the polynomial `P_a (t + a²)^i` has degree `< K - N`. -/
theorem natDegree_complClassFactor_mul_pow_lt [Nontrivial R] {q N K : ℕ} (a : ℕ) {i : ℕ}
    (hi : i < #(residuePoleIndices q (a : ℤ) N K)) :
    (complClassFactor R q (a : ℤ) N K * (X + C ((a : R) ^ 2)) ^ i).natDegree < K - N :=
  natDegree_complClassFactor_mul_lt ((monic_X_add_C _).pow _) (by rwa [natDegree_pow_X_add_C])

/-- For an odd prime `p` and any identification `e` of the rows of `classPowCoeffMatrix` with its
`h` columns, the determinant of the square matrix over `ℤ_p` is a unit: the polynomials
`P_a (t + a²)^i` form a `ℤ_p`-basis of the polynomials of degree `< h`. -/
theorem isUnit_det_classPowCoeffMatrix_padicInt {N K h : ℕ} (hp : Odd p)
    (e : (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) ≃ Fin h) :
    IsUnit ((classPowCoeffMatrix ℤ_[p] p N K h).submatrix id e).det := by
  have hM : (classPowCoeffMatrix ℤ_[p] p N K h).submatrix id e = Matrix.of fun ai aj ↦
      ((∏ k' ∈ ({ai.1}ᶜ : Finset (Fin (mStar p + 1))),
          residuePoleProduct ℤ_[p] p (k' : ℕ) N K) *
        (X + C (((ai.1 : ℕ) : ℤ_[p]) ^ 2)) ^ (ai.2 : ℕ)).coeff (e aj) := by
    ext ai aj
    rw [Matrix.submatrix_apply, id, classPowCoeffMatrix_apply, Matrix.of_apply,
      prod_compl_residuePoleProduct hp]
  rw [hM]
  exact isUnit_det_coeff_prod_compl_mul (fun _ ↦ residuePoleProduct_monic p _ N K)
    (fun _ ↦ natDegree_residuePoleProduct p _ N K)
    (pairwise_isCoprime_map_residue_residuePoleProduct hp N K)
    (fun k i ↦ (X + C (((k : ℕ) : ℤ_[p]) ^ 2)) ^ i) (fun _ _ ↦ (monic_X_add_C _).pow _)
    (fun _ _ ↦ natDegree_pow_X_add_C _ _) e

/-- For an odd prime `p`, the determinant of the integer matrix `classPowCoeffMatrix`, for any
identification `e` of its rows with its `h` columns, is a unit of `ℤ_p`. -/
theorem isUnit_det_classPowCoeffMatrix {N K h : ℕ} (hp : Odd p)
    (e : (Σ a : Fin (mStar p + 1), Fin #(residuePoleIndices p (a : ℕ) N K)) ≃ Fin h) :
    IsUnit ((((classPowCoeffMatrix ℤ p N K h).submatrix id e).det : ℤ) : ℤ_[p]) := by
  have := isUnit_det_classPowCoeffMatrix_padicInt hp e
  rwa [← map_classPowCoeffMatrix (Int.castRingHom ℤ_[p]), Matrix.submatrix_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast] at this

end Matrix

variable {n : ℕ}

omit [Fact p.Prime] in
/-- Conjugating `G_K` by `classPowCoeffMatrix` computes the inner form on the
polynomials `P_a (t + a²)^i`:
`(C G_K Cᵀ)_{(a,i),(c,j)} = Φ(P_a (t + a²)^i, P_c (t + c²)^j)`. -/
theorem classPowCoeffMatrix_mul_gramMatrix_mul_transpose_apply
    (ai cj : Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) :
    (classPowCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n) * gramMatrix n *
        (classPowCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose)
        ai cj =
      innerForm n
        (complClassFactor ℚ p (ai.1 : ℕ) (innerDegree n) (poleBound n) *
          (X + C (((ai.1 : ℕ) : ℚ) ^ 2)) ^ (ai.2 : ℕ))
        (complClassFactor ℚ p (cj.1 : ℕ) (innerDegree n) (poleBound n) *
          (X + C (((cj.1 : ℕ) : ℚ) ^ 2)) ^ (cj.2 : ℕ)) := by
  have hh : poleBound n - innerDegree n = matrixOrder n := by
    simp only [poleBound, innerDegree, matrixOrder]
    omega
  have hsum (bk : Σ a : Fin (mStar p + 1),
      Fin #(residuePoleIndices p (a : ℕ) (innerDegree n) (poleBound n))) :
      ∑ k : Fin (matrixOrder n),
        C (classPowCoeffMatrix ℚ p (innerDegree n) (poleBound n) (matrixOrder n) bk k) *
          X ^ (k : ℕ) =
        complClassFactor ℚ p (bk.1 : ℕ) (innerDegree n) (poleBound n) *
          (X + C (((bk.1 : ℕ) : ℚ) ^ 2)) ^ (bk.2 : ℕ) := by
    simp_rw [classPowCoeffMatrix_apply, C_mul_X_pow_eq_monomial]
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ monomial k (coeff _ k)),
      ← as_sum_range' _ _ (hh ▸ natDegree_complClassFactor_mul_pow_lt _ bk.2.2)]
  rw [← hsum ai, ← hsum cj, ← map_classPowCoeffMatrix (C : ℚ →+* ℚ[X]),
    map_mul_gramMatrix_mul_transpose_apply]

/-- For an odd prime `p`, `v_p^G(det (C G_K Cᵀ)) = v_p^G(Δ_K)`, where `C` is the coefficient
matrix of the polynomials `P_a (t + a²)^i`. -/
theorem vpG_map_det_classPowCoeffMatrix_mul_gramMatrix_mul_transpose (hp : Odd p) :
    vpG ((classPowCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        gramMatrix n *
        (classPowCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n)
          (matrixOrder n)).transpose).det.map (Rat.castHom ℚ_[p])) =
      vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  rw [← map_classPowCoeffMatrix (Int.castRingHom ℚ[X])]
  exact vpG_map_det_map_intCast_mul_gramMatrix_mul_transpose _
    (Fintype.equivFinOfCardEq (card_outerCoeffMatrix_rows_eq_matrixOrder hp n))
    (isUnit_det_classPowCoeffMatrix hp _)

/-- For `p > K`, each entry of `C G_K Cᵀ`, mapped to `ℚ_[p]`, has coefficients in `ℤ_[p]`. -/
theorem classPowCoeffMatrix_mul_gramMatrix_mul_transpose_map_mem_lifts (hn : 0 < n)
    (hp : poleBound n < p) :
    ∀ ai cj, ((classPowCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n) *
        gramMatrix n *
        (classPowCoeffMatrix ℚ[X] p (innerDegree n) (poleBound n) (matrixOrder n)).transpose)
        ai cj).map (Rat.castHom ℚ_[p]) ∈ lifts (PadicInt.Coe.ringHom (p := p)) := by
  have hK : poleBound n = 40 * n := rfl
  have hp7 : 7 ≤ p := by omega
  set N := innerDegree n with hN
  set K := poleBound n
  have hcast : (Rat.castHom ℚ_[p]) = algebraMap ℚ ℚ_[p] := by ext; simp
  intro ai cj
  set a : ℕ := (ai.1 : ℕ)
  set c : ℕ := (cj.1 : ℕ)
  have ha : a ≤ mStar p := Nat.lt_succ_iff.mp ai.1.2
  have hc : c ≤ mStar p := Nat.lt_succ_iff.mp cj.1.2
  set f : ℤ[X] := (X + C ((a : ℤ) ^ 2)) ^ (ai.2 : ℕ)
  set g : ℤ[X] := (X + C ((c : ℤ) ^ 2)) ^ (cj.2 : ℕ)
  set A : ℤ[X] := poleProductRange N ℤ ^ 5 * (complClassFactor ℤ p (a : ℤ) N K * f) *
    (complClassFactor ℤ p (c : ℤ) N K * g) with hAdef
  have hAq : poleProductRange N ℚ ^ 5 *
      (complClassFactor ℚ p (a : ℤ) N K * (X + C ((a : ℚ) ^ 2)) ^ (ai.2 : ℕ)) *
      (complClassFactor ℚ p (c : ℤ) N K * (X + C ((c : ℚ) ^ 2)) ^ (cj.2 : ℕ)) =
      A.map (Int.castRingHom ℚ) := by
    simp [hAdef, f, g, Polynomial.map_mul, Polynomial.map_pow, map_poleProductRange,
      map_complClassFactor]
  have hdA : (A.map (Int.castRingHom ℚ)).natDegree < 2 * p - 3 + (K - N) := by
    rw [← hAq]
    have h1 := natDegree_complClassFactor_mul_pow_lt (R := ℚ) (q := p) (N := N) (K := K) a
      ai.2.2
    have h2 := natDegree_complClassFactor_mul_pow_lt (R := ℚ) (q := p) (N := N) (K := K) c
      cj.2.2
    have h3 : (poleProductRange N ℚ ^ 5).natDegree ≤ 5 * N := by
      have := natDegree_pow_le (p := poleProductRange N ℚ) (n := 5)
      rwa [natDegree_poleProductRange] at this
    have h4 := natDegree_mul_le (p := poleProductRange N ℚ ^ 5 *
      (complClassFactor ℚ p (a : ℤ) N K * (X + C ((a : ℚ) ^ 2)) ^ (ai.2 : ℕ)))
      (q := complClassFactor ℚ p (c : ℤ) N K * (X + C ((c : ℚ) ^ 2)) ^ (cj.2 : ℕ))
    have h5 := natDegree_mul_le (p := poleProductRange N ℚ ^ 5)
      (q := complClassFactor ℚ p (a : ℤ) N K * (X + C ((a : ℚ) ^ 2)) ^ (ai.2 : ℕ))
    simp only [hN, K, innerDegree, poleBound] at h1 h2 h3 h4 h5 ⊢
    omega
  have hquot : (A.map (Int.castRingHom ℚ) /ₘ poleProduct (Icc (N + 1) K) ℚ).natDegree <
      2 * p - 3 := by
    rw [natDegree_divByMonic _ (monic_poleProduct _ ℚ), natDegree_poleProduct, Nat.card_Icc]
    omega
  rw [classPowCoeffMatrix_mul_gramMatrix_mul_transpose_apply, innerForm, hAq, hcast,
    map_rationalFunctional_eq_truncatedPoleFunctional hquot]
  by_cases hac : a = c
  · rw [hAdef, ← hac]
    exact truncatedPoleFunctional_complClassFactor_mul_mem_lifts hp7 hp ha f g
  · exact truncatedPoleFunctional_complClassFactor_mul_mem_lifts_of_ne hp7 ha hc hac f g

/-- **Primes above `K` do not divide `Δ_K`** (§5.12). Let `K = 40 n` with `n > 0` and let `p`
be a prime with `p > K`. Then `v_p^G(Δ_K) ≥ 0`. -/
@[zeta5irr "lem_out_above_K"]
theorem zero_le_vpG_gramDet_of_poleBound_lt (hn : 0 < n) (hp : poleBound n < p) :
    0 ≤ vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  have hK : poleBound n = 40 * n := rfl
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hentry := classPowCoeffMatrix_mul_gramMatrix_mul_transpose_map_mem_lifts hn hp
  set N := innerDegree n
  set K := poleBound n
  set M := classPowCoeffMatrix ℚ[X] p N K (matrixOrder n) * gramMatrix n *
    (classPowCoeffMatrix ℚ[X] p N K (matrixOrder n)).transpose with hM
  rw [← vpG_map_det_classPowCoeffMatrix_mul_gramMatrix_mul_transpose hodd]
  refine vpG_nonneg_of_mem_lifts ?_
  choose M' hM' using fun ai cj ↦ (mem_lifts _).mp (hentry ai cj)
  have hMap : M.map (Polynomial.map (Rat.castHom ℚ_[p])) =
      (Matrix.of M').map (Polynomial.map (PadicInt.Coe.ringHom (p := p))) := by
    ext ai cj : 1
    simp [hM']
  rw [show (M.det).map (Rat.castHom ℚ_[p]) =
      (M.map (Polynomial.map (Rat.castHom ℚ_[p]))).det from
      (RingHom.map_det (mapRingHom (Rat.castHom ℚ_[p])) M), hMap]
  exact (mem_lifts _).mpr ⟨(Matrix.of M').det, by
    rw [← coe_mapRingHom, RingHom.map_det]; rfl⟩

end Zeta5Irr
