/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.LocalEstimates.InSummand
public import Zeta5Irr.LocalEstimates.InUnitExpansion
public import Zeta5Irr.LocalEstimates.InNearpoleSize
public import Zeta5Irr.LocalEstimates.InPdiv
public import Zeta5Irr.LocalEstimates.InScale
public import Zeta5Irr.LocalFunctional.LocalIntegral
public import Zeta5Irr.LocalFunctional.CpVal

/-!
# Scaled factorizations and the entry valuations of the inner range

The entry valuations of the inner range (at a residue `σ ≠ 0` and at the residue `0`) are both
proved by writing the argument `f` of `δ^ext_{R^{(σ)}}` as `f = p^e V(z) h(pz)` with
`V ∈ ℤ_p[z]` of small degree and `h ∈ ℤ_p⟦z⟧`, and then applying the local integrality lemma.
This file holds the common part of the two arguments.

## Main definitions

* `Zeta5Irr.IsScaledFactorization`: the property `F = p^e V(z) h(pz)` with `deg V ≤ d`.

## Main results

* `Zeta5Irr.IsScaledFactorization.mul`, `.pow`, `.prod`: the property is multiplicative in
  `(e, d)`.
* `Zeta5Irr.isScaledFactorization_prod_farEps`: `∏_{s ∈ Σ^{(σ)}} ε_s = p^{#Σ^{(σ)}} h(pz)`.
* `Zeta5Irr.le_vpG_tauExt_deltaExt_of_isScaledFactorization`: if `f = p^e V(z) h(pz)` with
  `deg V ≤ p + 1`, then `v_p^G(p^{-4} τ^ext(δ^ext(p^{-k} f))) ≥ e - k - 4`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology
open scoped Finset

variable {p : ℕ} [Fact p.Prime]

/-! ### The substitution `h(z) ↦ h(pz)` -/

/-- `h(pz)` may be computed in `ℤ_p⟦z⟧` before mapping to `ℚ_p⟦z⟧`. -/
theorem map_rescale_eq_padicIntRescale (h : ℤ_[p]⟦X⟧) :
    PowerSeries.map PadicInt.Coe.ringHom (rescale (p : ℤ_[p]) h) = padicIntRescale p h := by
  ext k
  rw [coeff_padicIntRescale, coeff_map, coeff_rescale, map_mul, map_pow, map_natCast]
  rfl

/-- A constant is unchanged by `z ↦ pz`. -/
theorem padicIntRescale_C (x : ℤ_[p]) : padicIntRescale p (C x) = C (x : ℚ_[p]) := by
  ext k
  rw [coeff_padicIntRescale, coeff_C, coeff_C]
  split_ifs with hk
  · simp [hk]
  · simp

/-- `z ↦ pz`. -/
theorem padicIntRescale_X : padicIntRescale p X = C (p : ℚ_[p]) * X := by
  simp [padicIntRescale]

/-- The coefficients of `h(pz)` satisfy `|p^k h_k|_p ≤ p^{-k}`. -/
theorem norm_coeff_padicIntRescale_le (h : ℤ_[p]⟦X⟧) (k : ℕ) :
    ‖coeff k (padicIntRescale p h)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
  rw [coeff_padicIntRescale, norm_mul, norm_pow, Padic.norm_p, ← PadicInt.norm_def]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

/-- `h(pz) ∈ ℚ_p⟨z⟩`. -/
theorem padicIntRescale_mem_tateAlgebra (h : ℤ_[p]⟦X⟧) :
    padicIntRescale p h ∈ tateAlgebra p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [mem_tateAlgebra_iff]
  exact squeeze_zero (fun _ => norm_nonneg _) (norm_coeff_padicIntRescale_le h)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp))

/-! ### Scaled factorizations -/

variable (p) in
/-- `F = p^e V(z) H(z)` with `V ∈ ℤ_p[z]` of degree at most `d` and `H(z) = h(pz)` for some
`h ∈ ℤ_p⟦z⟧`. -/
def IsScaledFactorization (e d : ℕ) (F : ℚ_[p]⟦X⟧) : Prop :=
  ∃ V : Polynomial ℤ_[p], V.natDegree ≤ d ∧ ∃ H ∈ (padicIntRescale p).range,
    F = C ((p : ℚ_[p]) ^ e) * ((V.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) * H

namespace IsScaledFactorization

/-- The factorization property is multiplicative. -/
theorem mul {e d e' d' : ℕ} {F F' : ℚ_[p]⟦X⟧} (h : IsScaledFactorization p e d F)
    (h' : IsScaledFactorization p e' d' F') :
    IsScaledFactorization p (e + e') (d + d') (F * F') := by
  obtain ⟨V, hV, H, hH, rfl⟩ := h
  obtain ⟨V', hV', H', hH', rfl⟩ := h'
  refine ⟨V * V', (Polynomial.natDegree_mul_le).trans (add_le_add hV hV'), H * H',
    mul_mem hH hH', ?_⟩
  rw [Polynomial.map_mul, Polynomial.coe_mul, pow_add, map_mul]
  ring

/-- `1 = p^0 · 1 · 1`. -/
theorem one : IsScaledFactorization p 0 0 1 :=
  ⟨1, by simp, 1, one_mem _, by simp⟩

/-- A series of the form `h(pz)` has the factorization property with `e = d = 0`. -/
theorem of_mem_range {H : ℚ_[p]⟦X⟧} (hH : H ∈ (padicIntRescale p).range) :
    IsScaledFactorization p 0 0 H :=
  ⟨1, by simp, H, hH, by simp⟩

/-- The factorization property is stable under negation. -/
theorem neg {e d : ℕ} {F : ℚ_[p]⟦X⟧} (h : IsScaledFactorization p e d F) :
    IsScaledFactorization p e d (-F) := by
  obtain ⟨V, hV, H, hH, rfl⟩ := h
  exact ⟨V, hV, -H, neg_mem hH, by ring⟩

/-- The degree bound may be weakened. -/
theorem mono {e d d' : ℕ} {F : ℚ_[p]⟦X⟧} (h : IsScaledFactorization p e d F) (hd : d ≤ d') :
    IsScaledFactorization p e d' F := by
  obtain ⟨V, hV, H, hH, rfl⟩ := h
  exact ⟨V, hV.trans hd, H, hH, rfl⟩

/-- The factorization property is stable under powers. -/
theorem pow {e d : ℕ} {F : ℚ_[p]⟦X⟧} (h : IsScaledFactorization p e d F) (k : ℕ) :
    IsScaledFactorization p (k * e) (k * d) (F ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => simpa [pow_succ, add_mul] using ih.mul h

/-- The factorization property is stable under finite products. -/
theorem prod {ι : Type*} (s : Finset ι) {e d : ι → ℕ} {F : ι → ℚ_[p]⟦X⟧}
    (h : ∀ x ∈ s, IsScaledFactorization p (e x) (d x) (F x)) :
    IsScaledFactorization p (∑ x ∈ s, e x) (∑ x ∈ s, d x) (∏ x ∈ s, F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/-- `pz = p^1 · z · 1`. -/
theorem C_mul_X : IsScaledFactorization p 1 1 (C (p : ℚ_[p]) * X) :=
  ⟨Polynomial.X, by simp, 1, one_mem _, by simp⟩

end IsScaledFactorization

/-- The far factors: `∏_{s ∈ Σ^{(σ)}} ε_s = p^{#Σ^{(σ)}} h(pz)` for some `h ∈ ℤ_p⟦z⟧`. -/
theorem isScaledFactorization_prod_farEps (A : Finset ℤ) (σ : ℕ) :
    IsScaledFactorization p #(distFarPoles p A σ) 0 (∏ s ∈ distFarPoles p A σ, farEps s) := by
  set T := distFarPoles p A σ
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hnorm : ∀ x : T, ‖(p : ℚ_[p]) * x‖ = 1 := fun x => by
    rw [norm_mul, norm_of_mem_distFarPoles x.2, Padic.norm_p]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let m : T → ℤ_[p]ˣ := fun x =>
    (PadicInt.isUnit_iff (z := ⟨(p : ℚ_[p]) * (x : ℚ_[p]), (hnorm x).le⟩) |>.mpr (hnorm x)).unit
  have hm : ∀ x : T, ((m x : ℤ_[p]) : ℚ_[p]) / p = x := fun x => by
    change (p : ℚ_[p]) * (x : ℚ_[p]) / p = x
    field_simp
  obtain ⟨γ, -, hγ⟩ := exists_unit_expansion (p := p) (∅ : Finset Unit) T.attach
    (fun _ => 1) m
  simp only [Finset.prod_empty, one_mul, hm] at hγ
  rw [Finset.prod_attach T (fun x => C (p : ℚ_[p])⁻¹ * farEps x)] at hγ
  refine ⟨1, by simp, _, ⟨PowerSeries.mk γ, rfl⟩, ?_⟩
  have hsplit : ∏ s ∈ T, farEps s = ∏ s ∈ T, (C (p : ℚ_[p]) * (C (p : ℚ_[p])⁻¹ * farEps s)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp, map_one, one_mul]
  rw [hsplit, Finset.prod_mul_distrib, hγ, Finset.prod_const, Polynomial.map_one,
    Polynomial.coe_one, mul_one, map_pow]
  congr 1
  ext k
  rw [coeff_padicIntRescale, coeff_mk, coeff_mk]

/-! ### The local integrality lemma for a scaled factorization -/

/-- The tail of `h(pz)` beyond degree `J` has Gauss norm at most `p^{-J}`. -/
theorem tateNorm_trunc_sub_le (h : ℤ_[p]⟦X⟧) (J : ℕ) :
    tateNorm (((trunc J (padicIntRescale p h) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) -
      padicIntRescale p h) ≤ ((p : ℝ)⁻¹) ^ J := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine tateNorm_le_of_forall_norm_coeff_le fun k => ?_
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hk
  · simp only [sub_self, norm_zero]
    positivity
  · rw [zero_sub, norm_neg]
    exact (norm_coeff_padicIntRescale_le h k).trans
      (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp.le) (not_lt.mp hk))

/-- The partial sums of `∑_k p^k (V γ_k z^k)` are `V` times the truncations of
`∑_k p^k γ_k z^k`. -/
theorem sum_pow_smul_coe_map_eq (V : Polynomial ℤ_[p]) (h : ℤ_[p]⟦X⟧) (J : ℕ) :
    ∑ k ∈ Finset.range J, (p : ℚ_[p]) ^ k •
      (((V * Polynomial.C (coeff k h) * Polynomial.X ^ k).map PadicInt.Coe.ringHom :
        Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) =
      ((V.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) *
        ((trunc J (padicIntRescale p h) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
  rw [trunc_apply, ← Finset.range_eq_Ico]
  simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.coeToPowerSeries.ringHom_apply]
  rw [← Polynomial.coe_smul, ← Polynomial.coe_mul,
    coeff_padicIntRescale, ← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.smul_eq_C_mul, map_mul, map_pow]
  rw [show PadicInt.Coe.ringHom (coeff k h) = ((coeff k h : ℤ_[p]) : ℚ_[p]) from rfl]
  ring

/-- The partial sums `∑_{k < J} p^k V h_k z^k` converge to `V · h(pz)` in `ℚ_p⟨z⟩`. -/
theorem tendsto_tateNorm_sum_pow_smul_sub (V : Polynomial ℤ_[p]) (h : ℤ_[p]⟦X⟧) :
    Tendsto (fun J => tateNorm (∑ k ∈ Finset.range J, (p : ℚ_[p]) ^ k •
      ((((V * Polynomial.C (coeff k h) * Polynomial.X ^ k).map PadicInt.Coe.ringHom :
        Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧)) -
      ((V.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) * padicIntRescale p h))
      atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hHmem := padicIntRescale_mem_tateAlgebra h
  refine squeeze_zero (fun _ => tateNorm_nonneg _) (fun J => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1))
  rw [sum_pow_smul_coe_map_eq, ← mul_sub]
  calc _ ≤ tateNorm ((V.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) *
        tateNorm (((trunc J (padicIntRescale p h) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) -
          padicIntRescale p h) :=
        tateNorm_mul_le (coe_mem_tateAlgebra _) (sub_mem (coe_mem_tateAlgebra _) hHmem)
    _ ≤ 1 * ((p : ℝ)⁻¹) ^ J := mul_le_mul (tateNorm_map_coe_le_one V)
        (tateNorm_trunc_sub_le h J) (tateNorm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- For `p ≥ 7`, `Y_p = p^5 X + C_p ∈ ℤ_p[X]`. -/
theorem Yp_mem_lifts (hp : 7 ≤ p) :
    Yp p ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := p)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hC : ‖Cp p‖ ≤ 1 :=
    (norm_Cp_le hp).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hp1))
  have h1 : Polynomial.C ((p : ℚ_[p]) ^ 5) ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := p)) := by
    have := Polynomial.C_mem_lifts (PadicInt.Coe.ringHom (p := p)) ((p : ℤ_[p]) ^ 5)
    rwa [map_pow, map_natCast] at this
  have h2 : Polynomial.C (Cp p) ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := p)) :=
    Polynomial.C_mem_lifts (PadicInt.Coe.ringHom (p := p)) ⟨Cp p, hC⟩
  exact add_mem (mul_mem h1 (Polynomial.X_mem_lifts _)) h2

/-- Distinct integers of absolute value at most `M` with `2 M < p` differ by a `p`-adic unit. -/
theorem isUnit_intCast_sub_of_abs_le {M r r' : ℤ} (hp : 2 * M < p) (hr : |r| ≤ M)
    (hr' : |r'| ≤ M) (hne : r ≠ r') : IsUnit ((r - r' : ℤ) : ℤ_[p]) := by
  by_contra hu
  have hdvd := (PadicInt.norm_int_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hu)
  have : |r - r'| < p := by linarith [abs_sub r r']
  exact hne (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd this))

omit [Fact p.Prime] in
/-- An integer of absolute value at most `M < p` has reflected index below `p`. -/
theorem reflectIndex_lt_of_abs_le {M r : ℤ} (hp : M < p) (hr : |r| ≤ M) :
    reflectIndex r < p := by
  have : (reflectIndex r : ℤ) < p := by
    rcases le_or_gt 0 r with h0 | h0
    · rw [reflectIndex_of_nonneg h0]
      rw [abs_of_nonneg h0] at hr
      omega
    · rw [reflectIndex_of_neg h0]
      rw [abs_of_neg h0] at hr
      omega
  exact_mod_cast this

omit [Fact p.Prime] in
/-- If `K < p M` and `σ < p`, every near pole `m ∈ R^{(σ)}` has absolute value at most `M`. -/
theorem abs_le_of_mem_innerNearPoles {n M σ : ℕ} (hM0 : 0 < M) (hpM : poleBound n < p * M)
    (hσ : σ < p) {m : ℤ} (hm : m ∈ innerNearPoles p n σ) : |m| ≤ M := by
  have hpR : (poleBound n : ℝ) / M < p := by
    rw [div_lt_iff₀ (by exact_mod_cast hM0)]
    exact_mod_cast hpM
  obtain ⟨r, ⟨-, hr⟩, hrσ, rfl⟩ := (mem_innerNearPoles p).mp hm
  exact (abs_sub_div_le_of_modEq hM0 hpR (by positivity) (by exact_mod_cast hσ) hr hrσ).2

/-- **The local integrality lemma for a scaled factorization.** Let `p ≥ 7` be a prime and let
`R ⊆ ℤ` be a finite set of integers of absolute value at most `M`, where `2 M < p`. If
`f = p^e V(z) h(pz)` with `V ∈ ℤ_p[z]` of degree at most `p + 1` and `h ∈ ℤ_p⟦z⟧`, then
`v_p^G(p^{-4} τ_{Y_p}^ext(δ_R^ext(p^{-k} f))) ≥ e - k - 4`. -/
theorem le_vpG_tauExt_deltaExt_of_isScaledFactorization (hp7 : 7 ≤ p) {M : ℤ} (hM : 2 * M < p)
    {R : Finset ℤ} (hR : ∀ r ∈ R, |r| ≤ M) {e d : ℕ} {f : ℚ_[p]⟦X⟧}
    (hf : IsScaledFactorization p e d f) (hd : d ≤ p + 1) (k : ℕ) :
    (((e : ℤ) - k - 4 : ℤ) : WithTop ℤ) ≤
      vpG (((p : ℚ_[p]) ^ 4)⁻¹ • tauExt R (Yp p) (deltaExt R (((p : ℚ_[p]) ^ k)⁻¹ • f))) := by
  have hpQ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨V, hV, _, ⟨h, rfl⟩, rfl⟩ := hf
  set F : ℚ_[p]⟦X⟧ :=
    ((V.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) * padicIntRescale p h with hF
  have hsmul : ((p : ℚ_[p]) ^ k)⁻¹ • (C ((p : ℚ_[p]) ^ e) *
      ((V.map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) * padicIntRescale p h) =
      ((p : ℚ_[p]) ^ ((e : ℤ) - k)) • F := by
    rw [zpow_sub₀ hpQ, zpow_natCast, zpow_natCast, div_eq_inv_mul, smul_eq_C_mul, smul_eq_C_mul,
      hF, map_mul]
    ring
  rw [hsmul, tauExt_deltaExt_smul, smul_smul]
  have hFmem : F ∈ tateAlgebra p :=
    mul_mem (coe_mem_tateAlgebra _) (padicIntRescale_mem_tateAlgebra h)
  set U : ℕ → Polynomial ℤ_[p] := fun k => V * Polynomial.C (coeff k h) * Polynomial.X ^ k
    with hU
  have hlim := tendsto_tateNorm_sum_pow_smul_sub V h
  obtain ⟨q, hq, b, hb, hFq⟩ := exists_eq_mul_intPoleProduct_add_of_tendsto R U hFmem hlim
  have hδ := deltaExt_eq_of_eq_mul_add (q := ⟨q, hq⟩) hb hFq
  have hR' : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → IsUnit ((r - r' : ℤ) : ℤ_[p]) := fun r hr r' hr' =>
    isUnit_intCast_sub_of_abs_le hM (hR r hr) (hR r' hr')
  have hRp : ∀ r ∈ R, reflectIndex r < p := fun r hr =>
    reflectIndex_lt_of_abs_le (by omega) (hR r hr)
  have hU0 : (U 0).natDegree ≤ p + 1 := by
    have := Polynomial.natDegree_mul_C_le V (coeff 0 h)
    simp only [hU, pow_zero, mul_one]
    omega
  have hT := tauExt_mem_lifts_of_tendsto (by omega) hR' hRp (Yp_mem_lifts hp7) U hU0
    ⟨q, hq⟩ hb (hFq ▸ hlim)
  rw [hδ, Polynomial.smul_eq_C_mul]
  change _ ≤ gaussAddVal Padic.addValuation _
  rw [gaussAddVal_C_mul, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hpQ, addValuation_prime_zpow]
  have hT0 := vpG_nonneg_of_mem_lifts hT
  rw [show (e : ℤ) - k - 4 = -(4 : ℕ) + ((e : ℤ) - k) by push_cast; ring]
  exact le_add_of_nonneg_right hT0

end Zeta5Irr
