/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Fr
public import Zeta5Irr.LocalFunctional.SmallProdexp
public import Zeta5Irr.LocalFunctional.SmallFrVal
public import Zeta5Irr.LocalFunctional.VpG

/-!
# The variation of `F_{K,r}` near its deleted pole at a small prime

Let `p` be a prime, `K ≥ 1`, `r ∈ R_K` and `L₀ = ⌊log_p(2K)⌋`, and let `x ∈ ℤ_p` satisfy
`v_p(x - r) ≥ L₀ + 1`. Then
`v_p(F_{K,r}(x) - F_{K,r}(r)) ≥ v_p(x - r) - 2 L₀`.

For `s ∈ R_K \ {r}` we have `v_p(x - s) = v_p(r - s) ≤ L₀`. Writing
`η_s = (r - x) / (x - s)`, so that `v_p(η_s) ≥ v_p(x - r) - L₀ ≥ 1` and
`1 + η_s = (r - s) / (x - s)`, we get
`F_{K,r}(x) = F_{K,r}(r) ∏_{s ∈ R_K \ {r}} (1 + η_s)`. The product estimate for principal units
gives `v_p(∏ (1 + η_s) - 1) ≥ v_p(x - r) - L₀`, and `v_p(F_{K,r}(r)) ≥ -L₀` concludes.

## Main results

* `Zeta5Irr.sub_two_log_le_addValuation_poleDeletedProductAt_sub`:
  `v_p(F_{K,r}(x) - F_{K,r}(r)) ≥ n - 2⌊log_p(2K)⌋` whenever `p^n ∣ x - r`.

## Implementation notes

* The valuation is `Padic.addValuation`, valued in `ℤ ∪ {∞}`, so that the value `0` of
  `F_{K,r}(x) - F_{K,r}(r)` (for instance at `x = r`) is allowed.
* The hypothesis `v_p(x - r) ≥ L₀ + 1` is written `p ^ (L₀ + 1) ∣ x - r` in `ℤ_[p]`, and the
  conclusion is stated for every `n` with `p ^ n ∣ x - r`; taking `n = v_p(x - r)` when
  `x ≠ r` recovers the source's form, and for `x = r` both sides of the source are trivial.
* The source assumes `K ≥ 2` to make `R_K \ {r}` nonempty; the product estimate is used in the
  form with `Finset.inf`, which holds for the empty product as well, so no lower bound on `K`
  is needed. The hypothesis `K ≥ 1` is implied by `r ∈ R_K`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Nat

variable {p : ℕ} [Fact p.Prime]

variable {K : ℕ} {r : ℤ} {x : ℤ_[p]}

/-- If `r ∈ R_K`, `v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1` and `p ^ m ∣ x - r`, then the quantities
`η_s = (r - x) / (x - s)` for `s ∈ R_K \ {r}` satisfy `‖η_s‖ ≤ p^{-(m - ⌊log_p(2K)⌋)}`. -/
theorem norm_sub_div_sub_le_of_dvd (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) {m : ℕ}
    (hm : (p : ℤ_[p]) ^ m ∣ x - r) {s : ℤ} (hs : s ∈ (puncturedIcc K).erase r) :
    ‖((r : ℚ_[p]) - x) / ((x : ℚ_[p]) - s)‖ ≤
      (p : ℝ) ^ (-((m : ℤ) - Nat.log p (2 * K))) := by
  set L := Nat.log p (2 * K)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by positivity
  -- `‖x - r‖ ≤ p^{-m}`
  have hxr : ‖(r : ℚ_[p]) - x‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    rw [← norm_neg, neg_sub]
    exact norm_sub_intCast_le_of_pow_dvd hm
  -- `‖x - s‖ = ‖r - s‖ ≥ p^{-L}`
  have hxs := norm_sub_intCast_eq_of_mem_erase_puncturedIcc hr hx hs
  obtain ⟨hsr, hsK⟩ := mem_erase.1 hs
  have hrs0 : ((r - s : ℤ) : ℚ_[p]) ≠ 0 := by
    rw [Int.cast_ne_zero, sub_ne_zero]; exact hsr.symm
  have hlow : (p : ℝ) ^ (-(L : ℤ)) ≤ ‖((r - s : ℤ) : ℚ_[p])‖ := by
    have hrs := zpow_lt_norm_intCast_sub (p := p) hr hs
    rw [Padic.norm_eq_zpow_neg_valuation hrs0] at hrs ⊢
    rw [zpow_lt_zpow_iff_right₀ hp] at hrs
    rw [zpow_le_zpow_iff_right₀ hp]
    omega
  have hpos : 0 < ‖(x : ℚ_[p]) - s‖ := by rw [hxs]; exact norm_pos_iff.2 hrs0
  rw [norm_div, div_le_iff₀ hpos, neg_sub, zpow_sub₀ hp0.ne']
  calc ‖(r : ℚ_[p]) - x‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := hxr
    _ = (p : ℝ) ^ (L : ℤ) / (p : ℝ) ^ (m : ℤ) * (p : ℝ) ^ (-(L : ℤ)) := by
      rw [zpow_neg, zpow_neg, div_eq_mul_inv]
      field_simp
    _ ≤ (p : ℝ) ^ (L : ℤ) / (p : ℝ) ^ (m : ℤ) * ‖(x : ℚ_[p]) - s‖ := by
      rw [hxs]; gcongr

/-- **Variation of `F_{K,r}` near its deleted pole at a small prime.** If `r ∈ R_K` and
`v_p(x - r) ≥ ⌊log_p(2K)⌋ + 1`, then
`v_p(F_{K,r}(x) - F_{K,r}(r)) ≥ v_p(x - r) - 2⌊log_p(2K)⌋`; here `v_p(x - r)` is replaced by
any `n` with `p ^ n ∣ x - r`. -/
@[zeta5irr "lem_small_Fr_diff"]
theorem sub_two_log_le_addValuation_poleDeletedProductAt_sub (hr : r ∈ puncturedIcc K)
    (hx : (p : ℤ_[p]) ^ (Nat.log p (2 * K) + 1) ∣ x - r) {n : ℕ}
    (hn : (p : ℤ_[p]) ^ n ∣ x - r) :
    (((n : ℤ) - 2 * Nat.log p (2 * K) : ℤ) : WithTop ℤ) ≤
      Padic.addValuation
        (poleDeletedProductAt K r (x : ℚ_[p]) - poleDeletedProductAt K r (r : ℚ_[p])) := by
  set L := Nat.log p (2 * K)
  set η : ℤ → ℚ_[p] := fun s => ((r : ℚ_[p]) - x) / ((x : ℚ_[p]) - s) with hη
  -- the denominators do not vanish
  have hXs : ∀ s ∈ (puncturedIcc K).erase r, (x : ℚ_[p]) - s ≠ 0 := by
    intro s hs
    have := norm_sub_intCast_eq_of_mem_erase_puncturedIcc hr hx hs
    rw [← norm_ne_zero_iff, this, norm_ne_zero_iff, Int.cast_ne_zero, sub_ne_zero]
    exact (ne_of_mem_erase hs).symm
  have hRs : ∀ s ∈ (puncturedIcc K).erase r, (r : ℚ_[p]) - s ≠ 0 := by
    intro s hs
    rw [sub_ne_zero, Ne, Int.cast_inj]
    exact (ne_of_mem_erase hs).symm
  -- `F_{K,r}(x) - F_{K,r}(r) = F_{K,r}(r) (∏ (1 + η_s) - 1)`
  have hid : poleDeletedProductAt K r (x : ℚ_[p]) - poleDeletedProductAt K r (r : ℚ_[p]) =
      poleDeletedProductAt K r (r : ℚ_[p]) * (∏ s ∈ (puncturedIcc K).erase r, (1 + η s) - 1) := by
    have h1 : ∀ s ∈ (puncturedIcc K).erase r, 1 + η s = ((r : ℚ_[p]) - s) / ((x : ℚ_[p]) - s) := by
      intro s hs
      rw [hη]
      field_simp [hXs s hs]
      ring
    rw [prod_congr rfl h1, prod_div_distrib]
    have hX : ∏ s ∈ (puncturedIcc K).erase r, ((x : ℚ_[p]) - s) ≠ 0 := prod_ne_zero_iff.2 hXs
    have hR : ∏ s ∈ (puncturedIcc K).erase r, ((r : ℚ_[p]) - s) ≠ 0 := prod_ne_zero_iff.2 hRs
    simp only [poleDeletedProductAt]
    field_simp
  -- valuation bounds
  have hη0 : ∀ s ∈ (puncturedIcc K).erase r, 0 ≤ Padic.addValuation (η s) := by
    intro s hs
    have h := norm_sub_div_sub_le_of_dvd hr hx hx hs
    rw [show -(((L + 1 : ℕ) : ℤ) - L) = -1 by push_cast; ring] at h
    have := intCast_le_padicAddValuation_iff.2 h
    exact le_trans (by exact_mod_cast zero_le_one) this
  have hηn : ∀ s ∈ (puncturedIcc K).erase r,
      (((n : ℤ) - L : ℤ) : WithTop ℤ) ≤ Padic.addValuation (η s) :=
    fun s hs => intCast_le_padicAddValuation_iff.2 (norm_sub_div_sub_le_of_dvd hr hx hn hs)
  have hP : (((n : ℤ) - L : ℤ) : WithTop ℤ) ≤
      Padic.addValuation (∏ s ∈ (puncturedIcc K).erase r, (1 + η s) - 1) :=
    le_trans (Finset.le_inf hηn) (finset_inf_le_addValuation_prod_one_add_sub_one _ _ hη0)
  have hFr : ((-(L : ℤ) : ℤ) : WithTop ℤ) ≤
      Padic.addValuation (poleDeletedProductAt K r (r : ℚ_[p])) := by
    have h := neg_log_le_valuation_poleDeletedProductAt (p := p) (x := (r : ℤ_[p])) hr
      (by simp)
    rw [PadicInt.coe_intCast] at h
    rw [Padic.addValuation.apply (poleDeletedProductAt_self_ne_zero K r)]
    exact_mod_cast h
  rw [hid, AddValuation.map_mul]
  calc (((n : ℤ) - 2 * L : ℤ) : WithTop ℤ) = ((-(L : ℤ) : ℤ) : WithTop ℤ) +
        (((n : ℤ) - L : ℤ) : WithTop ℤ) := by rw [← WithTop.coe_add]; congr 1; ring
    _ ≤ _ := add_le_add hFr hP

end Zeta5Irr
