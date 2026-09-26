/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutCrossInt
public import Zeta5Irr.LocalEstimates.OutQ0
public import Zeta5Irr.LocalEstimates.OutW0
public import Zeta5Irr.LocalFunctional.SmallHarmVal
public import Zeta5Irr.DegreePositivity.DetSign
public import Zeta5Irr.LocalFunctional.VpG
public import Zeta5Irr.DegreePositivity.PartialFractions
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import Zeta5Irr.LocalEstimates.MA

/-!
# The outer range: the valuations of the class-`0` entries

Let `p ≥ 7` be a prime, fix the parameters `N = 3 n` and `K = 40 n`, and suppose `N < p` and
`K < 3 p`, so that `m_N = 0` and `m_K ∈ {1, 2}`. For `0 ≤ i, j < m_K - m_N` the entry of the
integral part of the outer form on the class-`0` block of the separating basis satisfies
`v_p^G(Φ₀(P_0 q_{0,i}, P_0 q_{0,j})) ≥ w_{0,i} + w_{0,j}`.

Write `S = {N + 1, …, K}` and `A = D_N ^ 5 (P_0 q_{0,i}) (P_0 q_{0,j})`, so that
`Φ₀(P_0 q_{0,i}, P_0 q_{0,j}) = μ₀(A /ₘ D_S) + ∑_{r ∈ S} A(-r²) / D_S'(-r²) · ν_r(X)`.
The polynomial part lies in `ℤ_p`. A node `r ∈ S` prime to `p` is a root of `P_0`, so only the
multiples `r = k p` contribute. At such a node `D_N(-r²)` and `P_0(-r²)` are integers,
`q_{0,i}(-r²) = ∏_{k' ≤ i} (k'² - k²) p²` has `v_p ≥ 2 i`, and
`D_S'(-r²) = ∏_{r' ∈ S, r' ≠ r} (r'² - r²)` has `v_p ≤ 2 m_K - 2`: a factor with `p ∤ r'` is a
`p`-adic unit, and a factor with `r' = k' p` is `(k'² - k²) p² = ±3 p²`. Finally
`v_p^G(ν_r) ≥ -1` since `v_p(r) = 1` and `v_p(H_r^{(5)}) ≥ -5`. Hence every residue term has
`v_p^G ≥ 2 i + 2 j - 2 m_K + 1`, and comparing with the values of `w_{0,i}` in the two cases
`m_K = 1, 2` gives the bound.

## Main results

* `Zeta5Irr.min_le_vpG_truncatedPoleFunctional_zeroClass`: for arbitrary `N` and `K < 3 p`,
  `v_p^G(μ_{0,X}(D_N ^ 5 (P_0 q_{0,i}) (P_0 q_{0,j}); {N + 1, …, K})) ≥
  min(0, 2 i + 2 j - 2 m_K + 1)`.
* `Zeta5Irr.outerWeightZero_add_le_vpG_outerIntegralForm`:
  `v_p^G(Φ₀(P_0 q_{0,i}, P_0 q_{0,j})) ≥ w_{0,i} + w_{0,j}`.

## Implementation notes

* Since `w_{0,i}` is rational, the bound is stated in `WithTop ℚ`, after pushing `v_p^G` along
  `ℤ → ℚ`.
* Of the source's hypotheses only `p ≥ 7`, `K < 3 p` and `N < p` (implied by `2 N < p`) are
  used. The conditions `K ∈ 40 ℤ_{>0}`, `p ≤ K`, `p² > 2 K` and `5 N ≤ 2 p - 2` are not needed:
  for `K < p` there are no indices `i < m_K - m_N`, and `K < 3 p ≤ p²` already gives
  `v_p(r) ≤ 1` for `r ≤ K`.
* The source treats `m_K = 1` and `m_K = 2` separately; here the residue terms are bounded
  uniformly by `2 i + 2 j - 2 m_K + 1`, and the case split only enters when comparing with
  `w_{0,i} + w_{0,j}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10 (The outer range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- An integer has nonnegative `p`-adic valuation. -/
private theorem padicValRat_intCast_nonneg (z : ℤ) : 0 ≤ padicValRat p (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Nat.cast_nonneg _

omit [Fact p.Prime] in
/-- An integer prime to `p` has `p`-adic valuation zero. -/
private theorem padicValRat_intCast_eq_zero {z : ℤ} (hz : ¬(p : ℤ) ∣ z) :
    padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz, Nat.cast_zero]

/-- `v_p((a p)² - (b p)²) = v_p(a² - b²) + 2`. -/
private theorem padicValRat_sq_sub_sq_mul {a b : ℕ} (h : (a : ℚ) ^ 2 - b ^ 2 ≠ 0) :
    padicValRat p (((a * p : ℕ) : ℚ) ^ 2 - ((b * p : ℕ) : ℚ) ^ 2) =
      padicValRat p (((a : ℤ) ^ 2 - (b : ℤ) ^ 2 : ℤ) : ℚ) + 2 := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : ((a * p : ℕ) : ℚ) ^ 2 - ((b * p : ℕ) : ℚ) ^ 2 =
      (((a : ℤ) ^ 2 - (b : ℤ) ^ 2 : ℤ) : ℚ) * (p : ℚ) ^ 2 := by push_cast; ring
  have h' : ((((a : ℤ) ^ 2 - (b : ℤ) ^ 2 : ℤ) : ℚ)) ≠ 0 := by push_cast; exact h
  rw [e, padicValRat.mul h' (pow_ne_zero _ hp), padicValRat.pow _,
    padicValRat.self (Fact.out : p.Prime).one_lt]
  push_cast
  ring

/-- `v_p` of a nonzero rational `x` viewed in `ℚ_p` is `v_p(x)`. -/
private theorem addValuation_ratCast {x : ℚ} (hx : x ≠ 0) :
    Padic.addValuation (x : ℚ_[p]) = padicValRat p x := by
  rw [Padic.addValuation.apply (by exact_mod_cast hx), Padic.valuation_ratCast]


/-- For `p ∣ r`, `0 < r < p²`, `p ≠ 2`, the pole value has `v_p^G(ν_r) ≥ -1`. -/
private theorem neg_one_le_vpG_poleValue (hp2 : p ≠ 2) {r : ℕ} (hpr : p ∣ r) (hr0 : 0 < r)
    (hr : r < p ^ 2) :
    (((-1 : ℤ)) : WithTop ℤ) ≤ vpG ((poleValue r).map (Rat.castHom ℚ_[p])) := by
  have hpp := (Fact.out : p.Prime)
  have hv1 : 1 ≤ padicValNat p r := one_le_padicValNat_of_dvd hr0.ne' hpr
  have hv2 : padicValNat p r ≤ 1 := by
    by_contra h
    have : p ^ 2 ∣ r := (padicValNat_dvd_iff_le hr0.ne').2 (by omega)
    exact absurd (Nat.le_of_dvd hr0 this) (by omega)
  have hr0' : (r : ℚ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hlog : Nat.log p r ≤ 1 := Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hr0.ne' hr)
  refine (le_gaussAddVal_iff _).2 fun m ↦ ?_
  rw [coeff_map]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [coeff_zero_poleValue, eq_ratCast]
      simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_neg, Rat.cast_mul]
      have hH := le_addValuation_harmonicFive (p := p) (le_refl r)
      have h4 : Padic.addValuation (((r : ℚ) ^ 4 : ℚ) : ℚ_[p]) = ((4 : ℤ) : WithTop ℤ) := by
        rw [addValuation_ratCast (pow_ne_zero _ hr0'), padicValRat.pow, padicValRat.of_nat]
        norm_cast
        omega
      have hq : Padic.addValuation (((1 / 4 : ℚ)) : ℚ_[p]) = ((0 : ℤ) : WithTop ℤ) := by
        rw [addValuation_ratCast (by norm_num)]
        congr 1
        rw [padicValRat.div one_ne_zero (by norm_num), padicValRat.one,
          show (4 : ℚ) = ((2 ^ 2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
          padicValNat.eq_zero_of_not_dvd fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq hpp
            Nat.prime_two).1 (hpp.dvd_of_dvd_pow h))]
        simp
      have h2r : Padic.addValuation (((1 / (2 * (r : ℚ)) : ℚ)) : ℚ_[p]) =
          ((-1 : ℤ) : WithTop ℤ) := by
        rw [addValuation_ratCast (by positivity)]
        congr 1
        have h2 : padicValRat p 2 = 0 := by
          rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
            padicValNat_primes hp2, Nat.cast_zero]
        rw [padicValRat.div one_ne_zero (by positivity), padicValRat.one,
          padicValRat.mul two_ne_zero hr0', h2, padicValRat.of_nat]
        omega
      have ha : ((-1 : ℤ) : WithTop ℤ) ≤
          Padic.addValuation (-((((r : ℚ) ^ 4 : ℚ) : ℚ_[p]) * ((harmonicFive r : ℚ) : ℚ_[p]))) := by
        rw [AddValuation.map_neg, AddValuation.map_mul, h4]
        refine le_trans ?_ (add_le_add le_rfl hH)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        omega
      refine le_trans ?_ (AddValuation.map_add _ _ _)
      refine le_min (le_trans ?_ (AddValuation.map_sub _ _ _)) h2r.ge
      exact le_min ha (by rw [hq]; exact WithTop.coe_le_coe.2 (by norm_num))
    · rw [coeff_one_poleValue, eq_ratCast, addValuation_ratCast (pow_ne_zero _ hr0'),
        padicValRat.pow, padicValRat.of_nat, WithTop.coe_le_coe]
      omega
  · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_poleValue_le r).trans_lt hm), map_zero,
      AddValuation.map_zero]
    exact le_top


/-- At a node `k p` the multiple-of-`p` pole product has `v_p(q_{0,i}(-(k p)²)) ≥ 2 i`,
provided the value is nonzero. -/
private theorem le_padicValRat_eval_multiplePoleProduct {k i : ℕ}
    (h : (multiplePoleProduct ℚ p i).eval (-((k * p : ℕ) : ℚ) ^ 2) ≠ 0) :
    2 * (i : ℤ) ≤ padicValRat p ((multiplePoleProduct ℚ p i).eval (-((k * p : ℕ) : ℚ) ^ 2)) := by
  have e : (multiplePoleProduct ℚ p i).eval (-((k * p : ℕ) : ℚ) ^ 2) =
      ∏ k' ∈ Icc 1 i, (((k' * p : ℕ) : ℚ) ^ 2 - ((k * p : ℕ) : ℚ) ^ 2) := by
    rw [eval_multiplePoleProduct]
    exact prod_congr rfl fun _ _ ↦ by ring
  rw [e] at h ⊢
  have hne := prod_ne_zero_iff.1 h
  rw [padicValRat_prod_of_ne_zero _ _ hne]
  calc 2 * (i : ℤ) = ∑ _k' ∈ Icc 1 i, (2 : ℤ) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun k' hk' ↦ by
      have hk : (k' : ℚ) ^ 2 - (k : ℚ) ^ 2 ≠ 0 := by
        intro h0
        apply hne k' hk'
        push_cast
        linear_combination (p : ℚ) ^ 2 * h0
      rw [padicValRat_sq_sub_sq_mul hk]
      linarith [padicValRat_intCast_nonneg (p := p) ((k' : ℤ) ^ 2 - (k : ℤ) ^ 2)]

/-- At a multiple `r` of `p` in `S = {N + 1, …, K}` with `K < 3 p` and `p ≠ 3`, the derivative
of the pole product has `v_p(D_S'(-r²)) ≤ 2 ⌊K / p⌋ - 2`. -/
private theorem padicValRat_eval_derivative_poleProduct_le (hp3 : p ≠ 3) {N K r : ℕ}
    (hK : K < 3 * p) (hr : r ∈ Icc (N + 1) K) (hpr : p ∣ r) :
    padicValRat p ((derivative (poleProduct (Icc (N + 1) K) ℚ)).eval (-(r : ℚ) ^ 2)) ≤
      2 * ((K / p : ℕ) : ℤ) - 2 := by
  have hpp := (Fact.out : p.Prime)
  rw [eval_derivative_poleProduct_neg_sq hr]
  have hne : ∀ r' ∈ (Icc (N + 1) K).erase r, ((r' : ℚ) ^ 2 - (r : ℚ) ^ 2) ≠ 0 := by
    intro r' hr' h
    have h1 : (r' : ℚ) ^ 2 = (r : ℚ) ^ 2 := sub_eq_zero.1 h
    have h2 : r' ^ 2 = r ^ 2 := by exact_mod_cast h1
    exact (mem_erase.1 hr').1 (Nat.pow_left_injective two_ne_zero h2)
  rw [padicValRat_prod_of_ne_zero _ _ hne]
  obtain ⟨hr1, hrK⟩ := mem_Icc.1 hr
  calc ∑ r' ∈ (Icc (N + 1) K).erase r, padicValRat p ((r' : ℚ) ^ 2 - (r : ℚ) ^ 2)
      ≤ ∑ r' ∈ (Icc (N + 1) K).erase r, if p ∣ r' then (2 : ℤ) else 0 := by
        refine sum_le_sum fun r' hr' ↦ ?_
        obtain ⟨hrr', hr'⟩ := mem_erase.1 hr'
        obtain ⟨hr'1, hr'K⟩ := mem_Icc.1 hr'
        split_ifs with h
        · obtain ⟨k, rfl⟩ := hpr
          obtain ⟨k', rfl⟩ := h
          have hk : k < 3 := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
          have hk' : k' < 3 := Nat.lt_of_mul_lt_mul_left (a := p) (by omega)
          have hk0 : k ≠ 0 := by rintro rfl; omega
          have hk'0 : k' ≠ 0 := by rintro rfl; omega
          have hkk : k ≠ k' := by rintro rfl; exact hrr' rfl
          have h3 : ((k' : ℤ) ^ 2 - (k : ℤ) ^ 2 = 3 ∨ (k' : ℤ) ^ 2 - (k : ℤ) ^ 2 = -3) := by
            interval_cases k <;> interval_cases k' <;> simp_all
          have hnd : ¬(p : ℤ) ∣ (k' : ℤ) ^ 2 - (k : ℤ) ^ 2 := by
            intro hd
            have : (p : ℤ) ∣ 3 := by
              rcases h3 with h3 | h3 <;> rw [h3] at hd
              · exact hd
              · exact (dvd_neg).1 hd
            have : p ∣ 3 := by exact_mod_cast this
            exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 this)
          have hkq : (k' : ℚ) ^ 2 - (k : ℚ) ^ 2 ≠ 0 := by
            intro h0
            apply hnd
            have : ((k' : ℤ) ^ 2 - (k : ℤ) ^ 2 : ℤ) = 0 := by exact_mod_cast h0
            rw [this]
            exact dvd_zero _
          rw [mul_comm p k', mul_comm p k, padicValRat_sq_sub_sq_mul hkq,
            padicValRat_intCast_eq_zero hnd]
          norm_num
        · have hnd : ¬(p : ℤ) ∣ ((r' : ℤ) ^ 2 - (r : ℤ) ^ 2) := by
            intro hd
            have h2 : (p : ℤ) ∣ (r : ℤ) ^ 2 :=
              dvd_pow (Int.natCast_dvd_natCast.2 hpr) two_ne_zero
            have h3 : (p : ℤ) ∣ ((r' ^ 2 : ℕ) : ℤ) := by
              push_cast
              simpa using dvd_add hd h2
            exact h (hpp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 h3))
          have e : ((r' : ℚ) ^ 2 - (r : ℚ) ^ 2) = (((r' : ℤ) ^ 2 - (r : ℤ) ^ 2 : ℤ) : ℚ) := by
            push_cast
            ring
          rw [e, padicValRat_intCast_eq_zero hnd]
    _ = 2 * (#(((Icc (N + 1) K).erase r).filter (p ∣ ·)) : ℤ) := by
        rw [sum_ite, sum_const_zero, sum_const, add_zero, nsmul_eq_mul, mul_comm]
    _ ≤ 2 * ((K / p : ℕ) : ℤ) - 2 := by
        rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨hr, hpr⟩)]
        have hle : #((Icc (N + 1) K).filter (Dvd.dvd p)) ≤ K / p := by
          rw [← Nat.Ioc_filter_dvd_card_eq_div]
          refine card_le_card (filter_subset_filter _ fun x hx ↦ ?_)
          obtain ⟨h1, h2⟩ := mem_Icc.1 hx
          exact mem_Ioc.2 ⟨by omega, h2⟩
        have hpos : 1 ≤ #((Icc (N + 1) K).filter (Dvd.dvd p)) :=
          card_pos.2 ⟨r, mem_filter.2 ⟨hr, hpr⟩⟩
        omega


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- **The class-`0` block of `μ_{0,X}`.** Let `p ≥ 7` be a prime, `S = {N + 1, …, K}` with
`K < 3 p`, and `A = D_N ^ 5 (P_0 q_{0,i}) (P_0 q_{0,j})`. Then
`v_p^G(μ_{0,X}(A; S)) ≥ min(0, 2 i + 2 j - 2 m_K + 1)`. -/
theorem min_le_vpG_truncatedPoleFunctional_zeroClass (hp7 : 7 ≤ p) {N K : ℕ} (hK : K < 3 * p)
    (i j : ℕ) :
    ((min 0 (2 * (i : ℤ) + 2 * j - 2 * (K / p : ℕ) + 1) : ℤ) : WithTop ℤ) ≤
      vpG (truncatedPoleFunctional p (Icc (N + 1) K)
        (poleProductRange N ℚ ^ 5 * (complClassFactor ℚ p 0 N K * multiplePoleProduct ℚ p i) *
          (complClassFactor ℚ p 0 N K * multiplePoleProduct ℚ p j))) := by
  have hpp := (Fact.out : p.Prime)
  set S := Icc (N + 1) K with hS
  set A := poleProductRange N ℚ ^ 5 * (complClassFactor ℚ p 0 N K * multiplePoleProduct ℚ p i) *
    (complClassFactor ℚ p 0 N K * multiplePoleProduct ℚ p j) with hA
  rw [truncatedPoleFunctional_apply, WithTop.coe_min]
  refine le_trans ?_ (min_le_gaussAddVal_add _ _ _)
  refine min_le_min ?_ ?_
  · -- the polynomial part lies in `ℤ_p`
    set Z : ℤ[X] := poleProductRange N ℤ ^ 5 *
      (complClassFactor ℤ p 0 N K * multiplePoleProduct ℤ p i) *
      (complClassFactor ℤ p 0 N K * multiplePoleProduct ℤ p j)
    have hZ : Z.map (Int.castRingHom ℚ) = A := by
      simp only [Z, A, Polynomial.map_mul, Polynomial.map_pow, map_poleProductRange,
        map_complClassFactor, map_multiplePoleProduct]
    rw [gaussAddVal_C, ← hZ, ← map_poleProduct S ℤ (Int.castRingHom ℚ),
      ← map_divByMonic _ (monic_poleProduct S ℤ)]
    have h := norm_truncatedMomentFunctional_map_intCast_le_one hp7 (Z /ₘ poleProduct S ℤ)
    by_cases hμ : truncatedMomentFunctional p ((Z /ₘ poleProduct S ℤ).map (Int.castRingHom ℚ)) = 0
    · rw [hμ, AddValuation.map_zero]
      exact le_top
    · rw [Padic.addValuation.apply hμ]
      exact WithTop.coe_le_coe.2 ((Padic.norm_le_one_iff_val_nonneg _).1 h)
  · -- every residue term is bounded below
    refine le_trans (Finset.le_inf fun r hr ↦ ?_) (finset_inf_le_gaussAddVal_sum _ _ _)
    obtain ⟨hr1, hrK⟩ := mem_Icc.1 hr
    change _ ≤ vpG _
    rw [← Rat.cast_smul_eq_qsmul ℚ_[p], smul_eq_C_mul, vpG, gaussAddVal_C_mul]
    set a := A.eval (-((r : ℚ) ^ 2)) with ha_def
    by_cases ha : a = 0
    · rw [ha, zero_div, Rat.cast_zero, AddValuation.map_zero, top_add]
      exact le_top
    have hev : a = (poleProductRange N ℚ).eval (-(r : ℚ) ^ 2) ^ 5 *
        ((complClassFactor ℚ p 0 N K).eval (-(r : ℚ) ^ 2) *
          (multiplePoleProduct ℚ p i).eval (-(r : ℚ) ^ 2)) *
        ((complClassFactor ℚ p 0 N K).eval (-(r : ℚ) ^ 2) *
          (multiplePoleProduct ℚ p j).eval (-(r : ℚ) ^ 2)) := by
      simp only [a, A, eval_mul, eval_pow]
    rw [hev] at ha
    have hpr : p ∣ r := by
      by_contra h
      refine ha ?_
      rw [eval_neg_sq_complClassFactor hr (by simpa [ZMod.natCast_eq_zero_iff] using h)]
      ring
    have hDne : (poleProductRange N ℚ).eval (-(r : ℚ) ^ 2) ≠ 0 := fun h ↦ ha (by rw [h]; ring)
    have hPne : (complClassFactor ℚ p 0 N K).eval (-(r : ℚ) ^ 2) ≠ 0 :=
      fun h ↦ ha (by rw [h]; ring)
    have hqine : (multiplePoleProduct ℚ p i).eval (-(r : ℚ) ^ 2) ≠ 0 :=
      fun h ↦ ha (by rw [h]; ring)
    have hqjne : (multiplePoleProduct ℚ p j).eval (-(r : ℚ) ^ 2) ≠ 0 :=
      fun h ↦ ha (by rw [h]; ring)
    -- the integral factors
    have hD : 0 ≤ padicValRat p ((poleProductRange N ℚ).eval (-(r : ℚ) ^ 2)) := by
      have : (poleProductRange N ℚ).eval (-(r : ℚ) ^ 2) =
          ((∏ e ∈ Icc 1 N, (-(r : ℤ) ^ 2 + (e : ℤ) ^ 2) : ℤ) : ℚ) := by
        rw [eval_poleProductRange]
        push_cast
        rfl
      rw [this]
      exact padicValRat_intCast_nonneg _
    have hP : 0 ≤ padicValRat p ((complClassFactor ℚ p 0 N K).eval (-(r : ℚ) ^ 2)) := by
      have : (complClassFactor ℚ p 0 N K).eval (-(r : ℚ) ^ 2) =
          (((complClassFactor ℤ p 0 N K).eval (-(r : ℤ) ^ 2) : ℤ) : ℚ) := by
        rw [eval_complClassFactor, eval_complClassFactor]
        push_cast
        rfl
      rw [this]
      exact padicValRat_intCast_nonneg _
    -- the factors `q_{0,i}`, `q_{0,j}`
    obtain ⟨k, hk⟩ := hpr
    have hrk : ((k * p : ℕ) : ℚ) = r := by rw [hk, mul_comm]
    have hqi := le_padicValRat_eval_multiplePoleProduct (p := p) (k := k) (i := i)
      (by rw [hrk]; exact hqine)
    have hqj := le_padicValRat_eval_multiplePoleProduct (p := p) (k := k) (i := j)
      (by rw [hrk]; exact hqjne)
    rw [hrk] at hqi hqj
    have hva : 2 * (i : ℤ) + 2 * j ≤ padicValRat p a := by
      rw [hev, padicValRat.mul (by positivity) (mul_ne_zero hPne hqjne),
        padicValRat.mul (pow_ne_zero _ hDne) (mul_ne_zero hPne hqine),
        padicValRat.mul hPne hqine, padicValRat.mul hPne hqjne, padicValRat.pow]
      nlinarith
    -- the derivative of the pole product
    have hdne := eval_derivative_poleProduct_ne_zero (K := ℚ) hr
    have hvd := padicValRat_eval_derivative_poleProduct_le (p := p) (by omega) hK hr ⟨k, hk⟩
    rw [← hS] at hvd
    -- the pole value
    have hr0 : 0 < r := by omega
    have hrp : r < p ^ 2 := by nlinarith
    have hν := neg_one_le_vpG_poleValue (p := p) (by omega) ⟨k, hk⟩ hr0 hrp
    have hc : a / (derivative (poleProduct S ℚ)).eval (-(r : ℚ) ^ 2) ≠ 0 := by
      rw [← hev] at ha
      exact div_ne_zero ha hdne
    rw [addValuation_ratCast hc]
    refine le_trans ?_ (add_le_add le_rfl hν)
    rw [← WithTop.coe_add, WithTop.coe_le_coe, padicValRat.div (by rwa [← hev] at ha) hdne]
    omega

/-- **The class-`0` entries of the outer range.** Let `p ≥ 7` be a prime with
`K = 40 n < 3 p` and `N = 3 n < p`, and let `0 ≤ i, j < m_K - m_N`. Then
`v_p^G(Φ₀(P_0 q_{0,i}, P_0 q_{0,j})) ≥ w_{0,i} + w_{0,j}`. -/
@[zeta5irr "lem_out_zero_val"]
theorem outerWeightZero_add_le_vpG_outerIntegralForm (hp7 : 7 ≤ p) {n i j : ℕ}
    (hKp : poleBound n < 3 * p) (hNp : innerDegree n < p)
    (hi : i < mA p (poleBound n) - mA p (innerDegree n))
    (hj : j < mA p (poleBound n) - mA p (innerDegree n)) :
    ((outerWeightZero (mA p (poleBound n)) (mA p (innerDegree n)) i +
        outerWeightZero (mA p (poleBound n)) (mA p (innerDegree n)) j : ℚ) : WithTop ℚ) ≤
      (vpG (outerIntegralForm p n
        (complClassFactor ℚ p 0 (innerDegree n) (poleBound n) * multiplePoleProduct ℚ p i)
        (complClassFactor ℚ p 0 (innerDegree n) (poleBound n) * multiplePoleProduct ℚ p j))).map
        ((↑) : ℤ → ℚ) := by
  have h := min_le_vpG_truncatedPoleFunctional_zeroClass hp7 (N := innerDegree n) hKp i j
  rw [← outerIntegralForm] at h
  have hmN : mA p (innerDegree n) = 0 := Nat.div_eq_of_lt hNp
  have hmK : mA p (poleBound n) < 3 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  rw [hmN, Nat.sub_zero] at hi hj
  have hw : outerWeightZero (mA p (poleBound n)) (mA p (innerDegree n)) i +
      outerWeightZero (mA p (poleBound n)) (mA p (innerDegree n)) j ≤
        ((min 0 (2 * (i : ℤ) + 2 * j - 2 * (poleBound n / p : ℕ) + 1) : ℤ) : ℚ) := by
    rw [Int.cast_min, hmN]
    simp only [mA] at hmK hi hj ⊢
    obtain h1 | h2 : poleBound n / p = 1 ∨ poleBound n / p = 2 := by omega
    · rw [outerWeightZero_of_sub_eq_one (by omega), outerWeightZero_of_sub_eq_one (by omega)]
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0 hj0
      rw [h1]
      norm_num
    · rw [outerWeightZero_of_sub_eq_two (by omega), outerWeightZero_of_sub_eq_two (by omega), h2]
      have hi1 : (i : ℚ) ≤ 1 := by exact_mod_cast (by omega : i ≤ 1)
      have hj1 : (j : ℚ) ≤ 1 := by exact_mod_cast (by omega : j ≤ 1)
      push_cast
      exact le_min (by linarith) (by linarith)
  exact coe_le_map_intCast_of_le hw h

end Zeta5Irr
