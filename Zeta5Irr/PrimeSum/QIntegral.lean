/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.QKM
public import Zeta5Irr.PrimeSum.NormMKMPos
public import Zeta5Irr.PrimeSum.NormVpGSmul
public import Zeta5Irr.PrimeSum.NormVpSKOuter
public import Zeta5Irr.LocalFunctional.VpGFK
public import Zeta5Irr.LocalEstimates.Inner
public import Zeta5Irr.LocalEstimates.Outer
public import Zeta5Irr.LocalEstimates.OutAboveK
public import Mathlib.NumberTheory.Padics.WithVal

/-!
# Integrality of `Q_{K,M}`

For every integer `M ≥ 40` and every `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, the polynomial
`Q_{K,M} = m_{K,M} F_K` has all its coefficients in `ℤ`.

The coefficients of `Q_{K,M}` are rational, and a rational number whose `p`-adic valuation is
nonnegative at every prime `p` is an integer, so it suffices to show `v_p^G(Q_{K,M}) ≥ 0` for
every prime `p`. Since `v_p^G(Q_{K,M}) = v_p(m_{K,M}) + v_p^G(F_K)` and
`v_p(m_{K,M}) = -L_p(K, M)` for `p ≤ 2h` and `0` otherwise, this is the inequality
`v_p^G(F_K) ≥ L_p(K, M)` for `p ≤ 2h`, which follows from the local bounds in each of the
four cases defining `L_p(K, M)`, and `v_p^G(F_K) ≥ 0` for `p > 2h`, where `v_p(S_K) = 0` and
`v_p^G(Δ_K) ≥ 0` since `p > K`.

## Main results

* `Zeta5Irr.localExponent_le_vpG_normalizedDet`: `v_p^G(F_K) ≥ L_p(K, M)` for `p ≤ 2h`.
* `Zeta5Irr.zero_le_vpG_normalizedDet`: `v_p^G(F_K) ≥ 0` for `p > 2h`.
* `Zeta5Irr.Rat.den_eq_one_of_forall_norm_padic_le_one`: a rational number that is a `p`-adic
  integer for every prime `p` is an integer.
* `Zeta5Irr.exists_coeff_normalizedPoly_eq_intCast`: every coefficient of `Q_{K,M}` is an
  integer.

## Implementation notes

* As elsewhere, `K = 40 n`, so the hypothesis `K ∈ 40 ℤ_{>0}` is automatic except for
  `K > 0`, which follows from `K ≥ 200 M²` and `M ≥ 40`.
* `Q_{K,M}` is a real polynomial; integrality is stated as: every coefficient is the image of
  an integer.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1 (The normalizing factor and integrality).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The `p`-adic valuation of a product of integer powers of primes `∏_{q ∈ s} q ^ e q` is
`e p` if `p ∈ s` and `0` otherwise. -/
theorem padicValRat_prod_zpow_of_prime {p : ℕ} [Fact p.Prime] {s : Finset ℕ}
    (hs : ∀ q ∈ s, q.Prime) (e : ℕ → ℤ) :
    padicValRat p (∏ q ∈ s, (q : ℚ) ^ e q) = if p ∈ s then e p else 0 := by
  rw [padicValRat_prod_of_ne_zero _ _ fun q hq ↦
    zpow_ne_zero _ (Nat.cast_ne_zero.2 (hs q hq).ne_zero), ← Finset.sum_ite_eq']
  simp_rw [padicValRat.zpow]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rcases eq_or_ne q p with rfl | hqp
  · simp [padicValRat.self (Fact.out : q.Prime).one_lt]
  · have := Fact.mk (hs q hq)
    simp [hqp, padicValRat.of_nat, padicValNat_primes hqp.symm]

/-- For a prime `p > 2h`, `v_p(S_K) = 0`. -/
theorem padicValRat_scalingFactor_eq_zero {n p : ℕ} [hp : Fact p.Prime]
    (hpn : 2 * matrixOrder n < p) : padicValRat p (scalingFactor n) = 0 := by
  have hp2 := hp.out.two_le
  have key : ∀ m, m < p → ∑ᶠ a ∈ Set.Ici 1, m / p ^ a = 0 := fun m hm => by
    rw [finsum_mem_Ici_one_div_pow_eq_div (by nlinarith), Nat.div_eq_of_lt hm]
  simp only [matrixOrder] at hpn
  rw [padicValRat_scalingFactor, key _ (by simp only [poleBound]; omega),
    key _ (by simp only [innerDegree]; omega),
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_Icc] at hi
      rw [key _ (by simp only [matrixOrder] at hi; omega)]]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [matrixOrder]
  · rw [padicValNat.eq_zero_of_not_dvd fun h => by have := Nat.le_of_dvd (by norm_num) h; omega]
    simp

variable {n M p : ℕ} [Fact p.Prime]

/-- `v_p^G(F_K) = v_p(S_K) + v_p^G(Δ_K)`. -/
theorem vpG_normalizedDet :
    vpG ((normalizedDet n).map (Rat.castHom ℚ_[p])) =
      (padicValRat p (scalingFactor n) : WithTop ℤ) +
        vpG ((gramDet n).map (Rat.castHom ℚ_[p])) := by
  rw [normalizedDet_eq_smul, vpG_map_smul (scalingFactor_ne_zero n)]

/-- **The local exponent bounds `v_p^G(F_K)`.** Let `M ≥ 40`, `K = 40 n ≥ 200 M²` and let
`p ≤ 2h` be a prime. Then `v_p^G(F_K) ≥ L_p(K, M)`. -/
theorem localExponent_le_vpG_normalizedDet (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    {z : ℤ} (hz : localExponent n M p = z) :
    (z : WithTop ℤ) ≤ vpG ((normalizedDet n).map (Rat.castHom ℚ_[p])) := by
  have hcast : (Rat.castHom ℚ_[p]) = algebraMap ℚ ℚ_[p] := by ext; simp
  have hp2 := (Fact.out : p.Prime).two_le
  have hK' : 320000 ≤ poleBound n := le_trans (by nlinarith) hK
  have hn : 0 < n := by simp only [poleBound] at hK'; omega
  by_cases h₁ : p * M ≤ poleBound n
  · rw [localExponent_of_mul_le_natLog h₁] at hz
    have hz' : z = -6 * matrixOrder n * Nat.log p (5 * poleBound n) -
        matrixOrder n * padicValNat p 24 :=
      Int.cast_injective (α := ℚ) (by
        rw [← hz]
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast])
    rw [hz', hcast]
    exact le_vpG_normalizedDet n
  rw [not_le] at h₁
  rw [vpG_normalizedDet]
  by_cases h₂ : 3 * p ≤ poleBound n
  · obtain ⟨g, hg⟩ := exists_innerExponent_eq_intCast n p M
    rw [localExponent_of_inner h₁ h₂, hg] at hz
    have hz' : z = padicValRat p (scalingFactor n) + g := by exact_mod_cast hz.symm
    have hM0 : (0 : ℚ) < M := by exact_mod_cast (show 0 < M by omega)
    have hin := innerExponent_le_vpG_gramDet (p := p) hM hK
      (by rw [div_lt_iff₀ hM0]; exact_mod_cast h₁)
      (by rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 3)]; exact_mod_cast (by omega : p * 3 ≤ _))
    rw [hg] at hin
    rw [hz', WithTop.coe_add]
    exact add_le_add le_rfl ((intCast_le_map_intCast_iff _ _).1 hin)
  rw [not_le] at h₂
  by_cases h₃ : p ≤ poleBound n
  · rw [localExponent_of_outer' h₁ h₂ h₃] at hz
    have hz' : z = padicValRat p (scalingFactor n) +
        outerExponent p (innerDegree n) (poleBound n) := by exact_mod_cast hz.symm
    have hKn : poleBound n = 40 * n := rfl
    have hNn : innerDegree n = 3 * n := rfl
    have hout := outerExponent_le_vpG_gramDet (p := p) (n := n) (by omega) h₃ h₂
      (by nlinarith) (by omega)
    rw [hz', WithTop.coe_add]
    exact add_le_add le_rfl hout
  rw [not_le] at h₃
  rw [localExponent_of_lt' h₁ h₃] at hz
  have hz' : z = padicValRat p (scalingFactor n) := by exact_mod_cast hz.symm
  rw [hz']
  exact le_add_of_nonneg_right (zero_le_vpG_gramDet_of_poleBound_lt hn h₃)

/-- For `n > 0` and a prime `p > 2h`, `v_p^G(F_K) ≥ 0`. -/
theorem zero_le_vpG_normalizedDet (hn : 0 < n) (hp : 2 * matrixOrder n < p) :
    0 ≤ vpG ((normalizedDet n).map (Rat.castHom ℚ_[p])) := by
  rw [vpG_normalizedDet, padicValRat_scalingFactor_eq_zero hp]
  simpa using zero_le_vpG_gramDet_of_poleBound_lt hn
    (by simp only [poleBound, matrixOrder] at hp ⊢; omega)

/-- A rational number whose image in `ℚ_p` has norm at most `1` for every prime `p` is an
integer. -/
theorem Rat.den_eq_one_of_forall_norm_padic_le_one {r : ℚ}
    (h : ∀ p : ℕ, ∀ _ : Fact p.Prime, ‖(r : ℚ_[p])‖ ≤ 1) : r.den = 1 := by
  by_contra hr
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hr
  have := Fact.mk hp
  exact Rat.padicValuation_le_one_iff.1
    ((Padic.norm_rat_le_one_iff_padicValuation_le_one p).1 (h p ‹_›)) hpd

/-- **Integrality of `Q_{K,M}`.** For every integer `M ≥ 40` and every `K = 40 n` with
`K ≥ 200 M²`, every coefficient of `Q_{K,M}` is an integer. -/
@[zeta5irr "prop_Q_integral"]
theorem exists_coeff_normalizedPoly_eq_intCast (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ poleBound n)
    (i : ℕ) : ∃ z : ℤ, (normalizedPoly n M).coeff i = z := by
  have hK' : 320000 ≤ poleBound n := le_trans (by nlinarith) hK
  have hn : 0 < n := by simp only [poleBound] at hK'; omega
  choose e he using exists_localExponent_eq_intCast n M
  set s := Nat.primesBelow (2 * matrixOrder n + 1)
  set q : ℚ := ∏ p ∈ s, (p : ℚ) ^ (-e p) with hqdef
  have hs : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp =>
    zpow_ne_zero _ (Nat.cast_ne_zero.2 (hs p hp).ne_zero)
  set r : ℚ := q * (normalizedDet n).coeff i
  have hcoeff : (normalizedPoly n M).coeff i = (r : ℝ) := by
    rw [normalizedPoly_eq_map (normalizingFactor_eq_ratCast fun p _ => he p), coeff_map,
      coeff_C_mul]
    rfl
  suffices hden : r.den = 1 by
    refine ⟨r.num, ?_⟩
    rw [hcoeff, ← Rat.cast_intCast (α := ℝ), (Rat.den_eq_one_iff r).1 hden]
  refine Rat.den_eq_one_of_forall_norm_padic_le_one fun p _ => ?_
  -- `v_p^G(Q_{K,M}) ≥ 0`
  have hv : 0 ≤ vpG ((C q * normalizedDet n).map (Rat.castHom ℚ_[p])) := by
    rw [← smul_eq_C_mul, vpG_map_smul hq0, hqdef, padicValRat_prod_zpow_of_prime hs]
    split_ifs with hps
    · have hle := localExponent_le_vpG_normalizedDet (p := p) hM hK (he p)
      induction h : vpG ((normalizedDet n).map (Rat.castHom ℚ_[p])) using WithTop.recTopCoe with
      | top => simp
      | coe v =>
        rw [h, WithTop.coe_le_coe] at hle
        rw [← WithTop.coe_add, WithTop.coe_nonneg]
        omega
    · rw [WithTop.coe_zero, zero_add]
      exact zero_le_vpG_normalizedDet hn
        (by
          rw [Nat.mem_primesBelow] at hps
          by_contra h
          exact hps ⟨by omega, Fact.out⟩)
  have hle := gaussAddVal_le Padic.addValuation _ i |>.trans' hv
  rw [coeff_map, coeff_C_mul] at hle
  by_cases hr : (r : ℚ_[p]) = 0
  · rw [hr, norm_zero]; exact zero_le_one
  rw [Padic.norm_le_one_iff_val_nonneg]
  change 0 ≤ Padic.addValuation (r : ℚ_[p]) at hle
  rw [Padic.addValuation.apply hr] at hle
  exact_mod_cast hle

end Zeta5Irr
