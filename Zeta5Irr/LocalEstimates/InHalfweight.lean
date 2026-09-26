/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InPullEntry
public import Zeta5Irr.LocalEstimates.InEntryVal
public import Zeta5Irr.LocalEstimates.InEntryValZero
public import Zeta5Irr.LocalEstimates.InCmpOrdinary
public import Zeta5Irr.LocalEstimates.InCmpZeroSource
public import Zeta5Irr.LocalFunctional.Distribution

/-!
# Every inner entry meets the sum of its two row weights

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, let `p` be a prime with `K / M < p ≤ K / 3`, and let
`0 ≤ a, c ≤ m°`, `0 ≤ i < L_a`, `0 ≤ j < L_c`. Then
`v_p^G(Φ(Ψ_{a,i}, Ψ_{c,j})) ≥ w_{a,i} + w_{c,j}`.

The entry `Φ(Ψ_{a,i}, Ψ_{c,j})` is `τ_X(g_{a,i,c,j}; {N < |r| ≤ K})`, which by distribution
(`p ≥ 5`) is the sum over the residues `0 ≤ σ < p` of the local summands `Ω_{a,i,c,j}(σ)`.
It suffices to bound each summand. For `σ = 0` the entry valuation at the residue `0` gives
`2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 12 m_N - 2 m_K + 1`, and each half
`2 θ_{a,i}(0) + 6 m_N - m_K + 1/2` is at least `w_{a,i}`. For `1 ≤ σ < p` let
`1 ≤ s ≤ m°` be the index with `σ ∈ {s, p - s}`; the entry valuation gives
`θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) - ℓ_K(s) - 4`, and each half
`θ_{a,i}(s) + b_s - (ℓ_K(s) + 4) / 2` is at least `w_{a,i}`.

## Main results

* `Zeta5Irr.innerWeight_add_innerWeight_le_vpG_innerForm`:
  `v_p^G(Φ(Ψ_{a,i}, Ψ_{c,j})) ≥ w_{a,i} + w_{c,j}`.

## Implementation notes

* The weights are rational and `v_p^G` takes values in `WithTop ℤ`, so the inequality is
  stated in `WithTop ℚ`, after mapping `v_p^G` along `ℤ → ℚ`. This is the form in which the
  determinant bound consumes it.
* The entry `Φ(Ψ_{a,i}, Ψ_{c,j}) ∈ ℚ[X]` is mapped to `ℚ_p[X]` before taking `v_p^G`.
* The source's condition `K ∈ 40 ℤ_{>0}` is encoded by `K = 40 n`; positivity follows from
  `K ≥ 200 M²`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6 (The inner range: the weights).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

/-- The half of the bound at the residue `0` attached to a row: for `a ≤ m°` and `i < L_a`,
`w_{a,i} ≤ 2 θ_{a,i}(0) + 6 m_N - m_K + 1/2`. -/
private theorem innerWeight_le_zeroSource {n p M a i : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : p.Prime) (hpK : (poleBound n : ℝ) / M < p)
    (hi : (i : ℤ) < classDimAt n p M a) :
    innerWeight n p M a i ≤ 2 * (classVanishingOrder n p M a i 0 : ℚ) +
      6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using innerWeight_zero_le_left n p M i
  · rw [classVanishingOrder_of_ne _ _ _ _ _ (by omega : (0 : ℕ) ≠ a), classDimAt_zero]
    rw [classDimAt_of_ne_zero _ _ _ (by omega)] at hi
    simpa using innerWeight_le_zeroClassDim hM hK hp hpK ha hi

/-- The half of the bound at an ordinary residue attached to a row: for `a ≤ m°`, `i < L_a`
and `1 ≤ s ≤ m°`, `w_{a,i} ≤ θ_{a,i}(s) + b_s - (ℓ_K(s) + 4) / 2`, with `b_s = 3 ℓ_N(s)`. -/
private theorem innerWeight_le_ordinarySource {n p M a i s : ℕ} (ha : a ≤ mStar p)
    (hi : (i : ℤ) < classDimAt n p M a) (hs₁ : 1 ≤ s) (hs : s ≤ mStar p) :
    innerWeight n p M a i ≤ (classVanishingOrder n p M a i s : ℚ) +
      3 * ellA p (innerDegree n) s - ((ellA p (poleBound n) s : ℚ) + 4) / 2 := by
  by_cases hsa : s = a
  · subst hsa
    rw [innerWeight_of_ne_zero n p M (by omega), classVanishingOrder_self, cast_innerClassOrder]
    simp
  · rw [classVanishingOrder_of_ne _ _ _ _ _ hsa, classDimAt_of_ne_zero _ _ _ (by omega)]
    have hZ : (innerClassDim n p M s : ℚ) + 3 * ellA p (innerDegree n) s = classDim n p M s := by
      have h₁ := innerClassDim_def n p M s
      have h₂ := classDim_def n p M s
      have h₃ := innerClassOrder_def p (innerDegree n) s
      have : innerClassDim n p M s + 3 * (ellA p (innerDegree n) s : ℤ) = classDim n p M s := by
        rw [h₁, h₂, h₃]; push_cast; ring
      exact_mod_cast this
    have key : innerWeight n p M a i ≤
        (classDim n p M s : ℚ) - ((ellA p (poleBound n) s : ℚ) + 4) / 2 := by
      rcases Nat.eq_zero_or_pos a with rfl | ha₁
      · exact innerWeight_zero_le n p M i (mem_Icc.2 ⟨hs₁, hs⟩)
      · rw [classDimAt_of_ne_zero _ _ _ (by omega)] at hi
        exact innerWeight_le_classDim_sub ha₁ ha hs₁ hs hi
    linarith

/-- **Every entry meets the sum of its two row weights.** Let `M ≥ 40`, let
`K = 40 n ≥ 200 M²`, let `p` be a prime with `K / M < p ≤ K / 3`, and let `0 ≤ a, c ≤ m°`,
`0 ≤ i < L_a`, `0 ≤ j < L_c`. Then `v_p^G(Φ(Ψ_{a,i}, Ψ_{c,j})) ≥ w_{a,i} + w_{c,j}`. -/
@[zeta5irr "lem_in_halfweight"]
theorem innerWeight_add_innerWeight_le_vpG_innerForm {p : ℕ} [Fact p.Prime] {n M a i c j : ℕ}
    (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n) (hpl : (poleBound n : ℝ) / M < p)
    (hpu : (p : ℝ) ≤ poleBound n / 3) (ha : a ≤ mStar p) (hc : c ≤ mStar p)
    (hi : (i : ℤ) < classDimAt n p M a) (hj : (j : ℤ) < classDimAt n p M c) :
    ((innerWeight n p M a i + innerWeight n p M c j : ℚ) : WithTop ℚ) ≤
      (vpG ((innerForm n (rowPoly n p M a i) (rowPoly n p M c j)).map
        (algebraMap ℚ ℚ_[p]))).map ((↑) : ℤ → ℚ) := by
  have hpp : p.Prime := Fact.out
  have hM0 : 0 < M := by omega
  obtain ⟨hKpM, hp200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le hM0 hK hpl
  have hodd : Odd p := hpp.odd_of_ne_two (by omega)
  have hmStar := two_mul_mStar_add_one hodd
  have hplQ : (poleBound n : ℚ) / M < p := by
    rw [div_lt_iff₀ (by exact_mod_cast hM0)]; exact_mod_cast hKpM
  -- the entry as the sum of the local summands
  rw [innerForm_rowPoly_eq_tauX, map_tauX_eq_tauDist (by omega)]
  change _ ≤ (vpG (tauDist p (poleAnnulus (innerDegree n) (poleBound n)) _)).map _
  rw [← sum_innerSummand, coe_le_map_intCast_iff]
  refine le_trans (Finset.le_inf fun σ hσ => ?_) (finset_inf_le_gaussAddVal_sum _ _ _)
  rw [mem_range] at hσ
  rcases Nat.eq_zero_or_pos σ with rfl | hσ₀
  · -- the residue `0`
    refine le_trans ?_ (le_vpG_innerSummand_zero hM hK hplQ ha hc hi hj)
    refine WithTop.coe_le_coe.2 (Int.ceil_le.2 ?_)
    have h₁ := innerWeight_le_zeroSource hM hK hpp hpl hi
    have h₂ := innerWeight_le_zeroSource hM hK hpp hpl hj
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_one]
    linarith
  · -- an ordinary residue `σ ∈ {s, p - s}`
    obtain ⟨s, hs₁, hs, hσs⟩ : ∃ s, 1 ≤ s ∧ s ≤ mStar p ∧ (σ = s ∨ σ = p - s) := by
      by_cases h : σ ≤ mStar p
      · exact ⟨σ, hσ₀, h, .inl rfl⟩
      · exact ⟨p - σ, by omega, by omega, .inr (by omega)⟩
    refine le_trans ?_ (le_vpG_innerSummand hM hK hpl hpu ha hc hi hj hs₁ hs hσs)
    refine WithTop.coe_le_coe.2 (Int.ceil_le.2 ?_)
    have h₁ := innerWeight_le_ordinarySource ha hi hs₁ hs
    have h₂ := innerWeight_le_ordinarySource hc hj hs₁ hs
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    linarith

end Zeta5Irr
