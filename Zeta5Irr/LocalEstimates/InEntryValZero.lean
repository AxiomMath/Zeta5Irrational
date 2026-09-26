/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InScaledFactorization
public import Zeta5Irr.LocalEstimates.InNearpolesZero
public import Zeta5Irr.LocalEstimates.InDegZero

/-!
# The entry valuation of the local summand at the residue `0`

Let `M ≥ 40`, `K = 40 n ≥ 200 M²`, let `p` be a prime with `K / M < p`, and let `0 ≤ a, c ≤ m°`,
`0 ≤ i < L_a`, `0 ≤ j < L_c`. The local summand `Ω_{a,i,c,j}(0)` at the residue `σ = 0` satisfies
`v_p^G(Ω_{a,i,c,j}(0)) ≥ 2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 12 m_N - 2 m_K + 1`.

The proof factors the argument `f = p^{-2(K-N)} g_{a,i,c,j}(pz) ∏_{s' ∈ Σ^{(0)}} ε_{s'}` of
`δ^ext_{R^{(0)}}` as `f = p^{β₀} V(z) H(z)`, where `V ∈ ℤ_p[z]` has degree at most
`D₀ = 5 + 2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 10 m_N`, `H(z) = h(pz)` for some `h ∈ ℤ_p⟦z⟧`, and
`β₀ = D₀ - #R^{(0)} = D₀ - (2 m_K - 2 m_N)`. Indeed each root `ρ` of the pulled-back integrand
`g_{a,i,c,j}` that is divisible by `p` contributes a factor `pz - ρ = p (z - ρ/p)`, each other
root a factor `pz - ρ` which is `h(pz)` for `h = z - ρ ∈ ℤ_p[z]`, and each `ε_{s'}`,
`s' = r/p` with `p ∤ r`, is `p` times a series of the form `h(pz)`. Writing `h = ∑ γ_k z^k`,
the polynomials `U_k = V γ_k z^k ∈ ℤ_p[z]` satisfy `V H = ∑ p^k U_k` in `ℚ_p⟨z⟩` and
`deg U_0 ≤ D₀ ≤ p + 1`, so by the local integrality lemma
`τ^ext_{Y_p}(δ^ext_{R^{(0)}}(V H)) ∈ ℤ_p[X]`, and scaling by `p^{β₀ - 4}` gives the bound.

## Main results

* `Zeta5Irr.le_vpG_innerSummand_zero`: the lower bound for `v_p^G(Ω_{a,i,c,j}(0))`.

## Implementation notes

* The source also assumes `p ≤ K / 3`; it is used there only to see that `R^{(0)}` is nonempty,
  which the local integrality lemma as formalized does not require, so the hypothesis is
  omitted. The hypothesis `K ∈ 40 ℤ_{>0}` is built in, as `K = 40 n`.
* Rather than listing the roots of `g_{a,i,c,j}` with multiplicity, the proof tracks, factor by
  factor, the property "`F = p^e V(z) h(pz)` with `V ∈ ℤ_p[z]` of degree at most `d` and
  `h ∈ ℤ_p⟦z⟧`", which is multiplicative in `(e, d)`. The unit property of the constant term in
  the unit expansion is not needed, since only an upper bound for `deg U_0` is used.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries
open scoped Finset

variable {p : ℕ} [Fact p.Prime]

/-- The factor `m² - (pz)²`: it is `p² (m'² - z²)` if `m = p m'`, and of the form `h(pz)`
otherwise. -/
private theorem isScaledFactorization_square (m : ℕ) :
    IsScaledFactorization p (if p ∣ m then 2 else 0) (if p ∣ m then 2 else 0)
      (C ((m : ℚ_[p]) ^ 2) - (C (p : ℚ_[p]) * X) ^ 2) := by
  split_ifs with hm
  · obtain ⟨m', rfl⟩ := hm
    refine ⟨Polynomial.C ((m' : ℤ_[p]) ^ 2) - Polynomial.X ^ 2, ?_, 1, one_mem _, ?_⟩
    · refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp
    · simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, mul_one]
      push_cast
      simp only [map_pow, map_mul, map_natCast]
      ring
  · refine .of_mem_range ⟨C ((m : ℤ_[p]) ^ 2) - X ^ 2, ?_⟩
    simp [padicIntRescale_X]


/-- The substitution `A(pz)`, computed in `ℚ[X]` and mapped to `ℚ_p⟦z⟧`, is the evaluation of
`A` at `pz`. -/
private theorem coe_map_comp_C_mul_X (A : Polynomial ℚ) :
    (((A.comp (Polynomial.C ((0 : ℕ) : ℚ) + Polynomial.C (p : ℚ) * Polynomial.X)).map
      (algebraMap ℚ ℚ_[p]) : Polynomial ℚ_[p]) :
      ℚ_[p]⟦X⟧) = A.eval₂ (PowerSeries.C.comp (algebraMap ℚ ℚ_[p]))
        (PowerSeries.C (p : ℚ_[p]) * PowerSeries.X) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB =>
    rw [Polynomial.add_comp, Polynomial.map_add, Polynomial.coe_add, hA, hB, Polynomial.eval₂_add]
  | monomial k a =>
    simp only [Polynomial.monomial_comp, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
      Polynomial.eval₂_monomial, RingHom.comp_apply, map_natCast, Nat.cast_zero, map_zero,
      zero_add, Polynomial.map_natCast]
    rw [show ((p : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) = (p : ℚ_[p]⟦X⟧) from
      map_natCast Polynomial.coeToPowerSeries.ringHom p]


/-- The value of `Ψ_{a,i}(-x²)` at `x ∈ ℚ_p⟦z⟧`. -/
private theorem eval₂_rowPoly (n M a i : ℕ) (x : ℚ_[p]⟦X⟧) :
    ((rowPoly n p M a i).comp (-Polynomial.X ^ 2)).eval₂ (PowerSeries.C.comp (algebraMap ℚ ℚ_[p]))
      x = (∏ c ∈ Finset.range (mStar p + 1) \ {a}, (C ((c : ℚ_[p]) ^ 2) - x ^ 2) ^
        rowPolyExponent n p M c) * (C ((a : ℚ_[p]) ^ 2) - x ^ 2) ^ i := by
  simp only [rowPoly_def, Polynomial.eval₂_comp, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_neg,
    Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply]
  simp only [map_pow, map_natCast, neg_add_eq_sub]

/-- The value of `g_{a,i,c,j}` at `x ∈ ℚ_p⟦z⟧`, as a product of factors `m² - x²`. -/
private theorem eval₂_pulledIntegrand (n M a i c j : ℕ) (x : ℚ_[p]⟦X⟧) :
    (pulledIntegrand n p M a i c j).eval₂ (PowerSeries.C.comp (algebraMap ℚ ℚ_[p])) x =
      C ((-1 : ℚ_[p]) ^ (poleBound n - innerDegree n)) * x ^ 5 *
        (∏ k ∈ Finset.Icc 1 (innerDegree n), (C ((k : ℚ_[p]) ^ 2) - x ^ 2)) ^ 5 *
        ((∏ c ∈ Finset.range (mStar p + 1) \ {a}, (C ((c : ℚ_[p]) ^ 2) - x ^ 2) ^
          rowPolyExponent n p M c) * (C ((a : ℚ_[p]) ^ 2) - x ^ 2) ^ i) *
        ((∏ c' ∈ Finset.range (mStar p + 1) \ {c}, (C ((c' : ℚ_[p]) ^ 2) - x ^ 2) ^
          rowPolyExponent n p M c') * (C ((c : ℚ_[p]) ^ 2) - x ^ 2) ^ j) := by
  rw [pulledIntegrand_def]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [eval₂_rowPoly, eval₂_rowPoly]
  simp only [poleProductRange, poleProduct, Polynomial.eval₂_comp, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, RingHom.comp_apply]
  simp only [map_pow, map_natCast, map_neg, map_one, neg_add_eq_sub]

omit [Fact p.Prime] in
/-- The number of `k ∈ [1, N]` divisible by `p`, counted twice, is `2 m_N`. -/
private theorem sum_Icc_ite_dvd (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (if p ∣ k then 2 else 0) = 2 * mA p N := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm,
    mA, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

/-- The factorization of `Ψ_{a,i}(-(pz)²)`: its roots divisible by `p` are `0`, with
multiplicity `2 θ_{a,i}(0)`. -/
private theorem isScaledFactorization_rowPoly (hodd : Odd p) {n M a : ℕ} (ha : a ≤ mStar p)
    (i : ℕ) :
    IsScaledFactorization p (if a = 0 then 2 * i else 2 * zeroClassDim M)
      (if a = 0 then 2 * i else 2 * zeroClassDim M)
      ((∏ c ∈ Finset.range (mStar p + 1) \ {a},
        (C ((c : ℚ_[p]) ^ 2) - (C (p : ℚ_[p]) * X) ^ 2) ^ rowPolyExponent n p M c) *
        (C ((a : ℚ_[p]) ^ 2) - (C (p : ℚ_[p]) * X) ^ 2) ^ i) := by
  have h := (IsScaledFactorization.prod (Finset.range (mStar p + 1) \ {a})
    fun c _ => (isScaledFactorization_square (p := p) c).pow (rowPolyExponent n p M c)).mul
      ((isScaledFactorization_square (p := p) a).pow i)
  have hlt := mStar_lt hodd
  have hdvd : ∀ c ≤ mStar p, (p ∣ c ↔ c = 0) := fun c hc =>
    ⟨fun h => Nat.eq_zero_of_dvd_of_lt h (by omega), fun h => h ▸ dvd_zero p⟩
  have hsum : (∑ c ∈ Finset.range (mStar p + 1) \ {a},
      rowPolyExponent n p M c * (if p ∣ c then 2 else 0)) + i * (if p ∣ a then 2 else 0) =
      if a = 0 then 2 * i else 2 * zeroClassDim M := by
    rw [Finset.sum_congr rfl (g := fun c => if c = 0 then rowPolyExponent n p M c * 2 else 0)
      fun c hc => by
        have : c ≤ mStar p := by
          simp only [Finset.mem_sdiff, Finset.mem_range] at hc
          omega
        simp only [hdvd c this]
        split_ifs <;> simp]
    rw [Finset.sum_ite_eq']
    simp only [hdvd a ha]
    by_cases h0 : a = 0
    · subst h0
      simp
      ring
    · simp [h0, Ne.symm h0, rowPolyExponent_zero]
      ring
  exact hsum ▸ h

/-- The factorization of `g_{a,i,c,j}(pz)`, with
`e = d = 5 + 10 m_N + 2 θ_{a,i}(0) + 2 θ_{c,j}(0)`. -/
private theorem isScaledFactorization_pulledIntegrand (hodd : Odd p) {n M a i c j : ℕ}
    (ha : a ≤ mStar p) (hc : c ≤ mStar p) :
    IsScaledFactorization p
      (5 + 10 * mA p (innerDegree n) + (if a = 0 then 2 * i else 2 * zeroClassDim M) +
        (if c = 0 then 2 * j else 2 * zeroClassDim M))
      (5 + 10 * mA p (innerDegree n) + (if a = 0 then 2 * i else 2 * zeroClassDim M) +
        (if c = 0 then 2 * j else 2 * zeroClassDim M))
      ((((pulledIntegrand n p M a i c j).comp
        (Polynomial.C ((0 : ℕ) : ℚ) + Polynomial.C (p : ℚ) * Polynomial.X)).map
          (algebraMap ℚ ℚ_[p]) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
  rw [coe_map_comp_C_mul_X, eval₂_pulledIntegrand]
  have hsign : IsScaledFactorization p 0 0
      (C ((-1 : ℚ_[p]) ^ (poleBound n - innerDegree n))) :=
    IsScaledFactorization.of_mem_range ⟨C ((-1 : ℤ_[p]) ^ (poleBound n - innerDegree n)), by
      rw [padicIntRescale_C]
      push_cast
      rfl⟩
  have h := (((hsign.mul (IsScaledFactorization.C_mul_X.pow 5)).mul
    ((IsScaledFactorization.prod (Finset.Icc 1 (innerDegree n))
      fun k _ => isScaledFactorization_square (p := p) k).pow 5)).mul
    (isScaledFactorization_rowPoly hodd (n := n) (M := M) ha i)).mul
    (isScaledFactorization_rowPoly hodd (n := n) (M := M) hc j)
  rw [sum_Icc_ite_dvd] at h
  have he : 0 + 5 * 1 + 5 * (2 * mA p (innerDegree n)) = 5 + 10 * mA p (innerDegree n) := by
    ring
  rw [he] at h
  exact h

/-- `#Σ_0 = #{r ∈ A : r ≢ 0 (mod p)}`. -/
private theorem card_distFarPoles_zero (A : Finset ℤ) :
    #(distFarPoles p A 0) = #{r ∈ A | ¬r ≡ 0 [ZMOD p]} := by
  classical
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [distFarPoles, Finset.card_image_of_injective]
  · congr 1
  · intro r r' h
    simpa [hp] using h

omit [Fact p.Prime] in
/-- `#R_0 = #{r ∈ A : r ≡ 0 (mod p)}`. -/
private theorem card_distNearPoles_zero (A : Finset ℤ) :
    #(distNearPoles p A 0) = #{r ∈ A | r ≡ 0 [ZMOD p]} := by
  rw [distNearPoles, Finset.card_image_of_injOn]
  · simp
  · intro r hr r' hr' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.cast_zero, sub_zero] at hr hr' h
    exact (Int.ediv_left_inj (Int.modEq_zero_iff_dvd.mp hr.2)
      (Int.modEq_zero_iff_dvd.mp hr'.2)).mp h

/-- `#Σ_0 + #R_0 = #A`. -/
private theorem card_distFarPoles_zero_add_card_distNearPoles_zero (A : Finset ℤ) :
    #(distFarPoles p A 0) + #(distNearPoles p A 0) = #A := by
  rw [card_distFarPoles_zero, card_distNearPoles_zero, add_comm]
  exact Finset.card_filter_add_card_filter_not _

omit [Fact p.Prime] in
/-- The multiples of `p` in `{N < |r| ≤ K}` number `2 m_K - 2 m_N`. -/
private theorem card_filter_poleAnnulus_modEq_zero_add {N K : ℕ} (h : N ≤ K) :
    #{r ∈ poleAnnulus N K | r ≡ 0 [ZMOD p]} + 2 * mA p N = 2 * mA p K := by
  rw [← card_filter_Icc_modEq_zero, ← card_filter_Icc_modEq_zero]
  exact card_filter_poleAnnulus_add_card_filter h _

/-- `2 θ_{a,i}(0)` is `2 i` if `a = 0` and `2 L₀` otherwise. -/
private theorem two_mul_classVanishingOrder_zero (n p M a i : ℕ) :
    2 * classVanishingOrder n p M a i 0 =
      ((if a = 0 then 2 * i else 2 * zeroClassDim M : ℕ) : ℤ) := by
  by_cases h0 : a = 0
  · subst h0
    simp
  · simp [classVanishingOrder, h0, Ne.symm h0]

/-- The exponent bookkeeping at the residue `0`: the bound `2 θ_{a,i}(0) + 2 θ_{c,j}(0) +
12 m_N - 2 m_K + 1` equals `β - 4`, where `p^β` is the scale of the factorized argument. -/
theorem two_mul_classVanishingOrder_zero_add_eq {n M a i c j : ℕ} :
    2 * classVanishingOrder n p M a i 0 + 2 * classVanishingOrder n p M c j 0 +
      12 * mA p (innerDegree n) - 2 * mA p (poleBound n) + 1 =
      (((5 + 10 * mA p (innerDegree n) +
        (if a = 0 then 2 * i else 2 * zeroClassDim M) +
        (if c = 0 then 2 * j else 2 * zeroClassDim M) +
        #(distFarPoles p (poleAnnulus (innerDegree n) (poleBound n)) 0) : ℕ) : ℤ) -
        ((2 * (poleBound n - innerDegree n) : ℕ) : ℤ) - 4) := by
  have hc1 := card_distFarPoles_zero_add_card_distNearPoles_zero (p := p)
    (poleAnnulus (innerDegree n) (poleBound n))
  have hc2 := card_poleAnnulus (innerDegree_le_poleBound n)
  have hc3 := card_distNearPoles_zero (p := p) (poleAnnulus (innerDegree n) (poleBound n))
  have hc4 := card_filter_poleAnnulus_modEq_zero_add (p := p) (innerDegree_le_poleBound n)
  rw [two_mul_classVanishingOrder_zero, two_mul_classVanishingOrder_zero]
  omega

/-- **The entry valuation at the residue `0`.** Let `M ≥ 40`, `K = 40 n ≥ 200 M²`, let `p` be
a prime with `K / M < p`, and let `0 ≤ a, c ≤ m°`, `0 ≤ i < L_a`, `0 ≤ j < L_c`. Then
`v_p^G(Ω_{a,i,c,j}(0)) ≥ 2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 12 m_N - 2 m_K + 1`. -/
@[zeta5irr "lem_in_entry_val_zero"]
theorem le_vpG_innerSummand_zero {n M a i c j : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : (poleBound n : ℚ) / M < p)
    (ha : a ≤ mStar p) (hc : c ≤ mStar p)
    (hi : (i : ℤ) < classDimAt n p M a) (hj : (j : ℤ) < classDimAt n p M c) :
    ((2 * classVanishingOrder n p M a i 0 + 2 * classVanishingOrder n p M c j 0 +
      12 * mA p (innerDegree n) - 2 * mA p (poleBound n) + 1 : ℤ) : WithTop ℤ) ≤
      vpG (innerSummand p n M a i c j 0) := by
  have hM0 : 0 < M := by omega
  obtain ⟨hpM, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le hM0 hK hp
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hdeg := five_add_classVanishingOrder_zero_add_mA_le hM hK hp hi hj
  rw [two_mul_classVanishingOrder_zero, two_mul_classVanishingOrder_zero] at hdeg
  have hf := (isScaledFactorization_pulledIntegrand (n := n) (M := M) (i := i) (j := j) hodd ha
    hc).mul (isScaledFactorization_prod_farEps (p := p)
      (poleAnnulus (innerDegree n) (poleBound n)) 0)
  rw [two_mul_classVanishingOrder_zero_add_eq, innerSummand]
  exact le_vpG_tauExt_deltaExt_of_isScaledFactorization (M := M) (by omega) (by omega)
    (fun _ => abs_le_of_mem_innerNearPoles hM0 hpM (Fact.out : p.Prime).pos) hf (by omega) _

end Zeta5Irr
