/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InScaledFactorization
public import Zeta5Irr.LocalEstimates.InDegOrd
public import Zeta5Irr.LocalEstimates.LaNonneg
public import Zeta5Irr.LocalEstimates.InNearpoles

/-!
# The entry valuations of the inner range

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, let `p` be a prime with `K / M < p ≤ K / 3`, and let
`0 ≤ a, c ≤ m°`, `0 ≤ i < L_a`, `0 ≤ j < L_c`, `1 ≤ s ≤ m°` and `σ ∈ {s, p - s}`. Then the local
summand `Ω_{a,i,c,j}(σ)` satisfies
`v_p^G(Ω_{a,i,c,j}(σ)) ≥ θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) - ℓ_K(s) - 4`.

The pulled-back integrand `g_{a,i,c,j}(x)` is `±` a product of linear factors `x - ρ`, `ρ ∈ ℤ`.
Under `x = σ + p z`, a factor with `ρ ≡ σ` becomes `p (z - (ρ - σ)/p)`, and any other factor is
`H(pz)` for `H = (σ - ρ) + z ∈ ℤ_p⟦z⟧`. Exactly `D = θ_{a,i}(s) + θ_{c,j}(s) + 5 ℓ_N(s)` factors
are of the first kind, so `g_{a,i,c,j}(σ + pz) = p^D V(z) H₁(pz)` with `V ∈ ℤ_p[z]` of degree at
most `D` and `H₁ ∈ ℤ_p⟦z⟧`. Similarly, by the unit expansion,
`∏_{s' ∈ Σ^{(σ)}} ε_{s'} = p^{#Σ^{(σ)}} H₂(pz)`, and `#Σ^{(σ)} = 2 (K - N) - (ℓ_K(s) - ℓ_N(s))`.
Hence the argument of `δ^ext_{R^{(σ)}}` is `p^β g` with `β = θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) -
ℓ_K(s)` and `g = V(z) H(pz) = ∑_k p^k U_k`, `U_k = H_k V z^k ∈ ℤ_p[z]`, `deg U_0 ≤ D ≤ p + 1`.
Division by `E_{R^{(σ)}}` and the local integrality lemma then show that
`τ^ext(δ^ext(g)) ∈ ℤ_p[X]`, and `Ω_{a,i,c,j}(σ) = p^{β - 4} τ^ext(δ^ext(g))`.

## Main results

* `Zeta5Irr.le_vpG_innerSummand`: the bound
  `v_p^G(Ω_{a,i,c,j}(σ)) ≥ θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) - ℓ_K(s) - 4`.

## Implementation notes

* The integers `K = 40 n` and `N = 3 n` are `poleBound n` and `innerDegree n`; the hypotheses
  `K / M < p ≤ K / 3` are stated in `ℝ`. Positivity of `n` follows from `K ≥ 200 M²`.
* The source writes the analytic numerator as `∑_k p^k U_k` with `U_k = u₀ γ_k V z^k`, where
  `∑_k p^k γ_k z^k` is the unit expansion of the product of the remaining factors. Here the
  remaining linear factors `(σ - ρ) + p z` are absorbed directly into a power series `H(pz)` with
  `H ∈ ℤ_p⟦z⟧`, and only the far factors `p^{-1} ε_{s'}` use the unit expansion. The local
  integrality lemma only needs `deg U_0 ≤ p + 1`, so neither the unit `γ_0` nor the exact degree
  of `U_0` is used.
* The division by `E_{R^{(σ)}}`, the formula for `δ^ext_R` and the local integrality lemma hold
  for every finite `R ⊆ ℤ`, so the nonemptiness of `R^{(σ)}` is not needed.
* That the only `0 ≤ c' ≤ m°` with `c' ≡ ±σ (mod p)` is `c' = s` is checked directly from
  `0 < s + c' < p` and `|s - c'| < p`, in place of the unit `c'^2 - s^2 ∈ ℤ_p^×`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The substitution `P ↦ P(σ + p z)`, from `ℚ[x]` to `ℚ_p⟦z⟧`. -/
private noncomputable def pullHom (σ : ℕ) : Polynomial ℚ →+* ℚ_[p]⟦X⟧ :=
  (Polynomial.coeToPowerSeries.ringHom).comp ((Polynomial.mapRingHom (algebraMap ℚ ℚ_[p])).comp
    (Polynomial.compRingHom (Polynomial.C (σ : ℚ) + Polynomial.C (p : ℚ) * Polynomial.X)))

private theorem pullHom_apply (σ : ℕ) (P : Polynomial ℚ) : pullHom p σ P =
    (((P.comp (Polynomial.C (σ : ℚ) + Polynomial.C (p : ℚ) * Polynomial.X)).map
      (algebraMap ℚ ℚ_[p]) : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) := rfl

/-- The factor `x - ρ` becomes `(σ - ρ) + p z`, which is `p (z - (ρ - σ)/p)` when `ρ ≡ σ` and
`H(pz)` with `H = (σ - ρ) + z` otherwise. -/
private theorem isScaledFactorization_pullHom_X_sub_C (σ : ℕ) (ρ : ℤ) :
    IsScaledFactorization p (if ρ ≡ σ [ZMOD p] then 1 else 0) (if ρ ≡ σ [ZMOD p] then 1 else 0)
      (pullHom p σ (Polynomial.X - Polynomial.C (ρ : ℚ))) := by
  have hpull : pullHom p σ (Polynomial.X - Polynomial.C (ρ : ℚ)) =
      PowerSeries.C (((σ - ρ : ℤ) : ℚ_[p])) + PowerSeries.C (p : ℚ_[p]) * PowerSeries.X := by
    rw [pullHom_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X, eq_ratCast, Rat.cast_natCast, Rat.cast_intCast,
      Int.cast_sub, Int.cast_natCast, map_sub]
    ring
  rw [hpull]
  split_ifs with h
  · obtain ⟨t, ht⟩ := (Int.ModEq.dvd h)
    refine ⟨Polynomial.X + Polynomial.C (t : ℤ_[p]), (Polynomial.natDegree_X_add_C _).le, 1,
      one_mem _, ?_⟩
    have ht' : ((σ - ρ : ℤ) : ℚ_[p]) = (p : ℚ_[p]) * t := by exact_mod_cast ht
    rw [ht', pow_one, mul_one, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, map_intCast, map_mul]
    ring
  · refine .of_mem_range ⟨PowerSeries.C (((σ - ρ : ℤ) : ℤ_[p])) + PowerSeries.X, ?_⟩
    rw [map_add, padicIntRescale_C, padicIntRescale_X]
    push_cast
    rfl

variable (p) in
/-- The number of the two integers `c, -c` that are congruent to `σ` modulo `p`. -/
private def nearCount (σ : ℕ) (c : ℤ) : ℕ :=
  (if c ≡ σ [ZMOD p] then 1 else 0) + (if -c ≡ σ [ZMOD p] then 1 else 0)

/-- The factor `c² - x² = -(x - c)(x + c)`. -/
private theorem isScaledFactorization_pullHom_quad (σ c : ℕ) :
    IsScaledFactorization p (nearCount p σ c) (nearCount p σ c)
      (pullHom p σ ((Polynomial.X + Polynomial.C ((c : ℚ) ^ 2)).comp (-Polynomial.X ^ 2))) := by
  have h : (Polynomial.X + Polynomial.C ((c : ℚ) ^ 2)).comp (-Polynomial.X ^ 2) =
      -((Polynomial.X - Polynomial.C (((c : ℤ)) : ℚ)) *
        (Polynomial.X - Polynomial.C ((-(c : ℤ) : ℤ) : ℚ))) := by
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    simp only [Int.cast_neg, Int.cast_natCast, map_neg, map_pow]
    ring
  rw [h, map_neg, map_mul]
  exact ((isScaledFactorization_pullHom_X_sub_C σ c).mul
    (isScaledFactorization_pullHom_X_sub_C σ (-(c : ℤ)))).neg

/-- The row polynomial part `Ψ_{a,i}(-x²)`. -/
private theorem isScaledFactorization_pullHom_rowPoly (σ n M a i : ℕ) :
    IsScaledFactorization p
      (∑ c' ∈ range (mStar p + 1) \ {a}, rowPolyExponent n p M c' * nearCount p σ c' +
        i * nearCount p σ a)
      (∑ c' ∈ range (mStar p + 1) \ {a}, rowPolyExponent n p M c' * nearCount p σ c' +
        i * nearCount p σ a)
      (pullHom p σ ((rowPoly n p M a i).comp (-Polynomial.X ^ 2))) := by
  rw [rowPoly_def, Polynomial.mul_comp, Polynomial.prod_comp]
  simp only [Polynomial.pow_comp]
  rw [map_mul, map_prod]
  simp only [map_pow (pullHom p σ)]
  refine IsScaledFactorization.mul (IsScaledFactorization.prod
    (d := fun c' => rowPolyExponent n p M c' * nearCount p σ c')
    (e := fun c' => rowPolyExponent n p M c' * nearCount p σ c') _ fun c' _ => ?_) ?_
  · exact (isScaledFactorization_pullHom_quad (p := p) σ c').pow _
  · exact (isScaledFactorization_pullHom_quad (p := p) σ a).pow i

/-- The pulled-back integrand `g_{a,i,c,j}(σ + pz)` as `p^D V(z) H(pz)`. -/
private theorem isScaledFactorization_pullHom_pulledIntegrand (σ n M a i c j : ℕ) :
    IsScaledFactorization p
      ((poleBound n - innerDegree n) * 0 + 5 * (if (0 : ℤ) ≡ σ [ZMOD p] then 1 else 0) +
        5 * ∑ k ∈ Icc 1 (innerDegree n), nearCount p σ k +
        (∑ c' ∈ range (mStar p + 1) \ {a}, rowPolyExponent n p M c' * nearCount p σ c' +
          i * nearCount p σ a) +
        (∑ c' ∈ range (mStar p + 1) \ {c}, rowPolyExponent n p M c' * nearCount p σ c' +
          j * nearCount p σ c))
      ((poleBound n - innerDegree n) * 0 + 5 * (if (0 : ℤ) ≡ σ [ZMOD p] then 1 else 0) +
        5 * ∑ k ∈ Icc 1 (innerDegree n), nearCount p σ k +
        (∑ c' ∈ range (mStar p + 1) \ {a}, rowPolyExponent n p M c' * nearCount p σ c' +
          i * nearCount p σ a) +
        (∑ c' ∈ range (mStar p + 1) \ {c}, rowPolyExponent n p M c' * nearCount p σ c' +
          j * nearCount p σ c))
      (pullHom p σ (pulledIntegrand n p M a i c j)) := by
  have hsign : Polynomial.C ((-1 : ℚ) ^ (poleBound n - innerDegree n)) =
      (-1) ^ (poleBound n - innerDegree n) := by simp
  have hD : (poleProductRange (innerDegree n) ℚ).comp (-Polynomial.X ^ 2) =
      ∏ k ∈ Icc 1 (innerDegree n),
        (Polynomial.X + Polynomial.C ((k : ℚ) ^ 2)).comp (-Polynomial.X ^ 2) := by
    rw [poleProductRange, poleProduct, Polynomial.prod_comp]
  rw [pulledIntegrand_def, hsign, hD]
  simp only [map_mul (pullHom p σ), map_pow (pullHom p σ), map_neg (pullHom p σ),
    map_one (pullHom p σ), map_prod (pullHom p σ)]
  have h1 : IsScaledFactorization p ((poleBound n - innerDegree n) * 0)
      ((poleBound n - innerDegree n) * 0) ((-1) ^ (poleBound n - innerDegree n)) :=
    IsScaledFactorization.one.neg.pow _
  have h2 : IsScaledFactorization p (5 * (if (0 : ℤ) ≡ σ [ZMOD p] then 1 else 0))
      (5 * (if (0 : ℤ) ≡ σ [ZMOD p] then 1 else 0)) (pullHom p σ Polynomial.X ^ 5) := by
    have h := (isScaledFactorization_pullHom_X_sub_C (p := p) σ 0).pow 5
    rwa [Int.cast_zero, map_zero, sub_zero] at h
  have h3 : IsScaledFactorization p (∑ k ∈ Icc 1 (innerDegree n), nearCount p σ k)
      (∑ k ∈ Icc 1 (innerDegree n), nearCount p σ k)
      (∏ k ∈ Icc 1 (innerDegree n), pullHom p σ
        ((Polynomial.X + Polynomial.C ((k : ℚ) ^ 2)).comp (-Polynomial.X ^ 2))) :=
    IsScaledFactorization.prod _ fun k _ => isScaledFactorization_pullHom_quad (p := p) σ k
  exact ((((h1.mul h2).mul (h3.pow 5)).mul (isScaledFactorization_pullHom_rowPoly σ n M a i)).mul
    (isScaledFactorization_pullHom_rowPoly σ n M c j))

/-! ### Counting the factors near `σ` -/

section Count

variable {s σ : ℕ} (hs₁ : 1 ≤ s) (hs : s ≤ mStar p) (hσ : σ = s ∨ σ = p - s)
include hs₁ hs hσ

omit [Fact p.Prime] in
private theorem modEq_or_modEq_neg : (σ : ℤ) ≡ s [ZMOD p] ∨ (σ : ℤ) ≡ -s [ZMOD p] := by
  rcases hσ with rfl | rfl
  · exact .inl rfl
  · refine .inr (Int.modEq_iff_dvd.mpr ⟨-1, ?_⟩)
    rw [mStar_def] at hs
    push_cast [show s ≤ p by omega]
    ring

omit [Fact p.Prime] in
private theorem not_modEq_and_modEq_neg (k : ℤ) : ¬(k ≡ s [ZMOD p] ∧ k ≡ -s [ZMOD p]) := by
  rintro ⟨h₁, h₂⟩
  have h := Int.eq_zero_of_abs_lt_dvd (h₁.symm.trans h₂).dvd
    (abs_lt.mpr ⟨by rw [mStar_def] at hs; omega, by rw [mStar_def] at hs; omega⟩)
  omega

omit [Fact p.Prime] in
/-- Exactly one of `k, -k` is congruent to `σ` when `k ≡ ±s`, and none otherwise. -/
private theorem nearCount_eq (k : ℤ) :
    nearCount p σ k = if k ≡ s [ZMOD p] ∨ k ≡ -s [ZMOD p] then 1 else 0 := by
  have hn := not_modEq_and_modEq_neg hs₁ hs hσ k
  have hneg : ∀ {x y : ℤ}, -x ≡ y [ZMOD p] ↔ x ≡ -y [ZMOD p] := fun {x y} =>
    ⟨fun h => by simpa using h.neg, fun h => by simpa using h.neg⟩
  unfold nearCount
  rcases modEq_or_modEq_neg hs₁ hs hσ with h | h
  · have e₁ : k ≡ σ [ZMOD p] ↔ k ≡ s [ZMOD p] := ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
    have e₂ : -k ≡ σ [ZMOD p] ↔ k ≡ -s [ZMOD p] := by
      rw [hneg]; exact ⟨fun h' => h'.trans h.neg, fun h' => h'.trans h.neg.symm⟩
    simp only [e₁, e₂]
    by_cases a : k ≡ s [ZMOD p] <;> by_cases b : k ≡ -s [ZMOD p] <;> simp_all
  · have e₁ : k ≡ σ [ZMOD p] ↔ k ≡ -s [ZMOD p] :=
      ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
    have e₂ : -k ≡ σ [ZMOD p] ↔ k ≡ s [ZMOD p] := by
      rw [hneg]
      exact ⟨fun h' => by simpa using h'.trans h.neg,
        fun h' => h'.trans (by simpa using h.neg.symm)⟩
    simp only [e₁, e₂]
    by_cases a : k ≡ s [ZMOD p] <;> by_cases b : k ≡ -s [ZMOD p] <;> simp_all

omit [Fact p.Prime] in
/-- For `0 ≤ c ≤ m°`, one of `c, -c` is congruent to `σ` iff `c = s`. -/
private theorem nearCount_natCast_of_le {c : ℕ} (hc : c ≤ mStar p) :
    nearCount p σ c = if c = s then 1 else 0 := by
  rw [nearCount_eq hs₁ hs hσ]
  congr 1
  rw [mStar_def] at hs hc
  refine propext ⟨?_, fun h => .inl (by rw [h])⟩
  rintro (h | h)
  · have := Int.eq_zero_of_abs_lt_dvd h.dvd (abs_lt.mpr ⟨by omega, by omega⟩)
    omega
  · have := Int.eq_zero_of_abs_lt_dvd h.dvd (abs_lt.mpr ⟨by omega, by omega⟩)
    omega

omit [Fact p.Prime] in
private theorem not_zero_modEq : ¬(0 : ℤ) ≡ σ [ZMOD p] := by
  intro h
  rw [mStar_def] at hs
  have := Int.eq_zero_of_abs_lt_dvd h.dvd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

omit [Fact p.Prime] in
private theorem sum_nearCount_Icc (A : ℕ) :
    ∑ k ∈ Icc 1 A, nearCount p σ k = ellA p A s := by
  rw [ellA, card_filter]
  refine sum_nbij (fun k : ℕ => (k : ℤ)) (fun k hk => ?_) (fun a _ b _ h => ?_)
    (fun x hx => ?_) (fun k _ => nearCount_eq hs₁ hs hσ (k : ℤ))
  · simp only [mem_Icc] at hk ⊢; omega
  · exact Nat.cast_injective h
  · simp only [coe_Icc, Set.mem_Icc, Set.mem_image] at hx ⊢
    exact ⟨x.toNat, by omega, by omega⟩

omit [Fact p.Prime] in
private theorem sum_rowPolyExponent_mul_nearCount {n M a i : ℕ} (ha : a ≤ mStar p) :
    ∑ c' ∈ range (mStar p + 1) \ {a}, rowPolyExponent n p M c' * nearCount p σ c' +
      i * nearCount p σ a = if s = a then i else rowPolyExponent n p M s := by
  rw [sum_congr rfl fun c' hc' => by
    rw [nearCount_natCast_of_le hs₁ hs hσ (c := c') (by
      simp only [Finset.mem_sdiff, mem_range] at hc'; omega)],
    nearCount_natCast_of_le hs₁ hs hσ ha]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', Finset.mem_sdiff, mem_range, mem_singleton]
  by_cases h : s = a
  · subst h; simp
  · simp [h, Ne.symm h, show s < mStar p + 1 by omega]

omit [Fact p.Prime] in
/-- The number of `r` with `N < |r| ≤ K` and `r ≡ σ` is `ℓ_K(s) - ℓ_N(s)`. -/
private theorem card_filter_poleAnnulus_add {N K : ℕ} (hNK : N ≤ K) :
    #{r ∈ poleAnnulus N K | r ≡ σ [ZMOD p]} + ellA p N s = ellA p K s := by
  have hσ' : (σ : ℤ) = s ∨ (σ : ℤ) = p - s := by
    rcases hσ with rfl | rfl
    · exact .inl rfl
    · rw [mStar_def] at hs; exact .inr (by push_cast [show s ≤ p by omega]; ring)
  rw [← card_filter_modEq_erase_Icc_eq_ellA_of_le_mStar (A := N) hs₁ hs hσ',
    ← card_filter_modEq_erase_Icc_eq_ellA_of_le_mStar (A := K) hs₁ hs hσ']
  have e : ∀ A : ℕ, {r ∈ (Icc (-(A : ℤ)) A).erase 0 | r ≡ σ [ZMOD p]} =
      {r ∈ Icc (-(A : ℤ)) A | 0 < |r| ∧ r ≡ σ [ZMOD p]} := fun A => by
    ext r
    simp only [mem_filter, mem_erase, abs_pos]
    tauto
  rw [e, e]
  exact card_filter_poleAnnulus_add_card_filter hNK _

end Count

/-- **The entry valuations of the inner range.** Let `M ≥ 40`, `K = 40 n ≥ 200 M²` and let `p`
be a prime with `K / M < p ≤ K / 3`. Let `0 ≤ a, c ≤ m°`, `i < L_a`, `j < L_c`, `1 ≤ s ≤ m°` and
`σ ∈ {s, p - s}`. Then
`v_p^G(Ω_{a,i,c,j}(σ)) ≥ θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) - ℓ_K(s) - 4`. -/
@[zeta5irr "lem_in_entry_val"]
theorem le_vpG_innerSummand {n M a c i j s σ : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (hpl : (poleBound n : ℝ) / M < p) (hpu : (p : ℝ) ≤ poleBound n / 3)
    (ha : a ≤ mStar p) (hc : c ≤ mStar p) (hi : (i : ℤ) < classDimAt n p M a)
    (hj : (j : ℤ) < classDimAt n p M c) (hs₁ : 1 ≤ s) (hs : s ≤ mStar p)
    (hσ : σ = s ∨ σ = p - s) :
    ((classVanishingOrder n p M a i s + classVanishingOrder n p M c j s +
        6 * ellA p (innerDegree n) s - ellA p (poleBound n) s - 4 : ℤ) : WithTop ℤ) ≤
      vpG (innerSummand p n M a i c j σ) := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  -- the size of `p`
  have hM0 : 0 < M := by omega
  obtain ⟨hKpM, hp200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le hM0 hK hpl
  have h3p : 3 * p ≤ poleBound n := by
    have : (3 * p : ℝ) ≤ poleBound n := by linarith
    exact_mod_cast this
  have hσp : σ < p := by rw [mStar_def] at hs; omega
  have hNK := innerDegree_le_poleBound n
  -- the orders `θ` at `s` are the exponents of the row polynomials
  have hplQ : (poleBound n : ℚ) / M < p := by
    rw [div_lt_iff₀ (by exact_mod_cast hM0)]; exact_mod_cast hKpM
  have hpuQ : (p : ℚ) ≤ poleBound n / 3 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : p * 3 ≤ poleBound n)
  have hθ : ∀ {a i : ℕ}, (((if s = a then i else rowPolyExponent n p M s : ℕ)) : ℤ) =
      classVanishingOrder n p M a i s := by
    intro a i
    by_cases h : s = a
    · subst h; simp
    · simp only [h, ↓reduceIte]
      rw [classVanishingOrder_of_ne _ _ _ _ _ h,
        classDimAt_of_ne_zero _ _ _ (by omega : s ≠ 0),
        cast_rowPolyExponent_of_ne_zero _ _ _ (by omega)
          ((two_le_innerClassDim hM hK hplQ hpuQ hs₁ hs).trans' (by norm_num))]
  -- Steps 1 and 2: the pulled-back integrand
  have hG := isScaledFactorization_pullHom_pulledIntegrand (p := p) σ n M a i c j
  simp only [not_zero_modEq hs₁ hs hσ, ↓reduceIte] at hG
  rw [mul_zero, zero_add, mul_zero, zero_add,
    sum_nearCount_Icc hs₁ hs hσ, sum_rowPolyExponent_mul_nearCount hs₁ hs hσ ha,
    sum_rowPolyExponent_mul_nearCount hs₁ hs hσ hc] at hG
  set D := 5 * ellA p (innerDegree n) s + (if s = a then i else rowPolyExponent n p M s) +
    (if s = c then j else rowPolyExponent n p M s) with hD
  have hDp : D + 0 ≤ p + 1 := by
    have h := classVanishingOrder_add_add_le hM hK hpp hpl hi hj hs₁
    rw [← hθ, ← hθ] at h
    omega
  -- Step 3: the far poles
  have hf := hG.mul
    (isScaledFactorization_prod_farEps (poleAnnulus (innerDegree n) (poleBound n)) σ)
  set Rf := {r ∈ poleAnnulus (innerDegree n) (poleBound n) | r ≡ σ [ZMOD p]}
  have hRf : #Rf + ellA p (innerDegree n) s = ellA p (poleBound n) s :=
    card_filter_poleAnnulus_add hs₁ hs hσ hNK
  have hSig : #(innerFarPoles p n σ) + #Rf = 2 * (poleBound n - innerDegree n) := by
    have h₁ := card_filter_add_card_filter_not (s := poleAnnulus (innerDegree n) (poleBound n))
      (fun r => r ≡ σ [ZMOD p])
    rw [card_poleAnnulus hNK] at h₁
    have hinj : Function.Injective fun r : ℤ => ((r - σ : ℤ) : ℚ_[p]) / p := by
      intro x y h
      have h' : ((x - σ : ℤ) : ℚ_[p]) = ((y - σ : ℤ) : ℚ_[p]) := by
        simpa [div_left_inj' hp0] using h
      have := Int.cast_injective h'
      omega
    have h₂ : #(innerFarPoles p n σ) =
        #{r ∈ poleAnnulus (innerDegree n) (poleBound n) | ¬r ≡ σ [ZMOD p]} := by
      classical
      simp only [innerFarPoles, distFarPoles]
      convert card_image_of_injective _ hinj
    rw [h₂, add_comm]
    convert h₁ using 2
  -- Steps 4 to 6: the local integrality lemma
  have key := le_vpG_tauExt_deltaExt_of_isScaledFactorization (M := M) (by omega) (by omega)
    (fun _ => abs_le_of_mem_innerNearPoles hM0 hKpM hσp) hf hDp
    (2 * (poleBound n - innerDegree n))
  rw [innerSummand, ← pullHom_apply]
  convert key using 2
  rw [← hθ, ← hθ]
  simp only [innerFarPoles] at hSig
  simp only [D, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

end Zeta5Irr
