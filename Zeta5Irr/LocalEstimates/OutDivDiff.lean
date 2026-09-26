/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutNuInt
public import Zeta5Irr.LocalEstimates.OutNuCongr

/-!
# Divided differences of pole values at a split class

Let `p` be an odd prime, `1 ≤ a < p`, and `u₁, u₂ ∈ ℤ_p` with `u₁ ≡ u₂ (mod p)`. Then
`(u₁ ν_a(X) - u₂ ν_{p-a}(X)) / p ∈ ℤ_p[X]`, where `ν_j` is the pole value. Indeed
`u₁ ν_a - u₂ ν_{p-a} = u₁ (ν_a - ν_{p-a}) + (u₁ - u₂) ν_{p-a}`; the first term lies in
`p ℤ_p[X]` by the congruence `ν_a ≡ ν_{p-a} (mod p)`, and the second because `ν_{p-a}` is
`p`-integral and `u₁ - u₂ ∈ p ℤ_p`.

## Main results

* `Zeta5Irr.inv_smul_sub_poleValue_mem_lifts_padicInt`:
  `p⁻¹ • (u₁ ν_a - u₂ ν_{p-a}) ∈ ℤ_p[X]`.
* `Zeta5Irr.eval_smul_poleValue_mem_lifts`, `Zeta5Irr.sum_pair_div_smul_poleValue_mem_lifts`:
  for `B ∈ ℤ[t]`, the residues of `B / D_T` at a single pole `j < p`, or at a split pair of
  poles `T = {a, p - a}`, are `p`-integral.

## Implementation notes

* Membership in `ℤ_p[X]` of a polynomial in `ℚ_p[X]` is stated as membership in
  `Polynomial.lifts (ℤ_p → ℚ_p)`, and division by `p` as the scalar action of `p⁻¹`.
* The source assumes `p ≥ 7` and `1 ≤ a ≤ m° = (p - 1) / 2`. The statement holds for every odd
  prime `p` and every `1 ≤ a < p`, and is stated in that generality; oddness of `p` is the
  hypothesis `p ≠ 2`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.9 (The outer range: congruences at a split class).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- **Divided differences of pole values at a split class are `p`-integral.** For an odd prime
`p`, `1 ≤ a < p` and `u₁, u₂ ∈ ℤ_p` with `u₁ - u₂ ∈ p ℤ_p`, the polynomial
`(u₁ ν_a(X) - u₂ ν_{p-a}(X)) / p`, viewed in `ℚ_p[X]`, lies in `ℤ_p[X]`. -/
@[zeta5irr "lem_out_div_diff"]
theorem inv_smul_sub_poleValue_mem_lifts_padicInt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ}
    (ha : 1 ≤ a) (hap : a < p) {u₁ u₂ : ℤ_[p]} (hu : u₁ - u₂ ∈ Ideal.span {(p : ℤ_[p])}) :
    (p : ℚ_[p])⁻¹ • (C (u₁ : ℚ_[p]) * (poleValue a).map (Rat.castHom ℚ_[p]) -
      C (u₂ : ℚ_[p]) * (poleValue (p - a)).map (Rat.castHom ℚ_[p])) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  have hpr : p.Prime := Fact.out
  rw [lifts_iff_coeff_lifts]
  intro n
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hu
  let F : ℤ_[p] := ⟨((poleValue a).coeff n : ℚ_[p]), norm_coeff_poleValue_le_one hp hap n⟩
  let G : ℤ_[p] := ⟨((poleValue (p - a)).coeff n : ℚ_[p]),
    norm_coeff_poleValue_le_one hp (by omega) n⟩
  have hFG : F - G ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    refine PadicInt.mem_nonunits.2 ?_
    have := norm_coeff_poleValue_sub_poleValue_lt_one hp ha hap n
    rwa [coeff_sub, Rat.cast_sub] at this
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hFG
  obtain ⟨y, hy⟩ := hFG
  refine ⟨u₁ * y + w * G, ?_⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hpr.ne_zero
  have hy' : (F : ℚ_[p]) - G = y * p := by exact_mod_cast (congrArg ((↑) : ℤ_[p] → ℚ_[p]) hy).symm
  have hw' : (u₁ : ℚ_[p]) - u₂ = w * p := by exact_mod_cast (congrArg ((↑) : ℤ_[p] → ℚ_[p]) hw).symm
  have hFc : (F : ℚ_[p]) = ((poleValue a).coeff n : ℚ_[p]) := rfl
  have hGc : (G : ℚ_[p]) = ((poleValue (p - a)).coeff n : ℚ_[p]) := rfl
  rw [coeff_smul, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_map, coeff_map, smul_eq_mul]
  have key : ((u₁ * y + w * G : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p])⁻¹ *
      ((u₁ : ℚ_[p]) * ((poleValue a).coeff n : ℚ_[p]) -
        (u₂ : ℚ_[p]) * ((poleValue (p - a)).coeff n : ℚ_[p])) := by
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_mul, ← hFc, ← hGc]
    rw [eq_inv_mul_iff_mul_eq₀ hp0]
    linear_combination -(u₁ : ℚ_[p]) * hy' - (G : ℚ_[p]) * hw'
  exact key

/-- An integer multiple of a polynomial in `ℤ_p[X]` lies in `ℤ_p[X]`. -/
theorem intCast_smul_mem_lifts {p : ℕ} [Fact p.Prime] {z : ℤ} {f : ℚ_[p][X]}
    (hf : f ∈ lifts (PadicInt.Coe.ringHom (p := p))) :
    ((z : ℚ) • f) ∈ lifts (PadicInt.Coe.ringHom (p := p)) := by
  rw [Int.cast_smul_eq_zsmul]
  rw [lifts_iff_liftsRing] at hf ⊢
  exact zsmul_mem hf z

/-- Evaluating the image in `ℚ[t]` of `B ∈ ℤ[t]` at `-m²` gives the integer `B(-m²)`. -/
theorem eval_neg_sq_map_intCast (B : ℤ[X]) (m : ℕ) :
    (B.map (Int.castRingHom ℚ)).eval (-((m : ℚ) ^ 2)) = ((B.eval (-(m : ℤ) ^ 2) : ℤ) : ℚ) := by
  rw [show -((m : ℚ) ^ 2) = ((-(m : ℤ) ^ 2 : ℤ) : ℚ) by push_cast; ring, eval_intCast_map]
  rfl

/-- **The residue at a single pole is integral.** For an odd prime `p`, `j < p` and
`B ∈ ℤ[t]`, `B(-j²) ν_j(X) ∈ ℤ_p[X]`. -/
theorem eval_smul_poleValue_mem_lifts {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {j : ℕ} (hj : j < p)
    (B : ℤ[X]) :
    (B.map (Int.castRingHom ℚ)).eval (-((j : ℚ) ^ 2)) • (poleValue j).map (Rat.castHom ℚ_[p]) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  rw [eval_neg_sq_map_intCast]
  exact intCast_smul_mem_lifts (poleValue_mem_lifts_padicInt hp hj)

/-- **The residues at a split pair of poles are integral.** For an odd prime `p`, `1 ≤ a` with
`2 a < p` and `B ∈ ℤ[t]`, the sum of the residues of `B / D_{{a, p - a}}` at the poles `a` and
`p - a`, `∑_{k ∈ {a, p - a}} B(-k²) / D_{{a, p - a} ∖ {k}}(-k²) ν_k(X)`, lies in `ℤ_p[X]`. -/
theorem sum_pair_div_smul_poleValue_mem_lifts {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℕ}
    (ha : 1 ≤ a) (h2a : 2 * a < p) (Bz : ℤ[X]) :
    ∑ k ∈ ({a, p - a} : Finset ℕ), ((Bz.map (Int.castRingHom ℚ)).eval (-((k : ℚ) ^ 2)) /
        (poleProduct (({a, p - a} : Finset ℕ).erase k) ℚ).eval (-((k : ℚ) ^ 2))) •
          (poleValue k).map (Rat.castHom ℚ_[p]) ∈ lifts (PadicInt.Coe.ringHom (p := p)) := by
  have hne : a ≠ p - a := by omega
  have he1 : ({a, p - a} : Finset ℕ).erase a = {p - a} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
  have he2 : ({a, p - a} : Finset ℕ).erase (p - a) = {a} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
  have hsmul (q : ℚ) (f : ℚ_[p][X]) : q • f = C (q : ℚ_[p]) * f := by
    ext k
    simp [coeff_C_mul, Rat.smul_def]
  rw [Finset.sum_pair hne, he1, he2, eval_neg_sq_map_intCast, eval_neg_sq_map_intCast]
  simp only [poleProduct, Finset.prod_singleton, eval_add, eval_X, eval_C, hsmul]
  set u₁ : ℤ := Bz.eval (-(a : ℤ) ^ 2)
  set u₂ : ℤ := Bz.eval (-((p - a : ℕ) : ℤ) ^ 2)
  have hu : (u₁ : ℤ_[p]) - u₂ ∈ Ideal.span {(p : ℤ_[p])} := by
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub (-(a : ℤ) ^ 2) (-((p - a : ℕ) : ℤ) ^ 2) Bz
    have hdiff : -(a : ℤ) ^ 2 - -((p - a : ℕ) : ℤ) ^ 2 = p * ((p - 2 * a : ℕ) : ℤ) := by
      push_cast [show a ≤ p by omega, show 2 * a ≤ p by omega]
      ring
    rw [hdiff] at hc
    refine Ideal.mem_span_singleton'.2 ⟨((p - 2 * a : ℕ) : ℤ_[p]) * (c : ℤ_[p]), ?_⟩
    have : ((u₁ - u₂ : ℤ) : ℤ_[p]) = ((p * ((p - 2 * a : ℕ) : ℤ) * c : ℤ) : ℤ_[p]) := by
      rw [← hc]
    push_cast at this
    rw [this]
    ring
  have hmem := inv_smul_sub_poleValue_mem_lifts_padicInt hp2 ha (by omega) hu
  have hd : ‖((p - 2 * a : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 (Nat.coprime_of_lt_prime (by omega) (by omega) Fact.out)
  have hinv : ‖((p - 2 * a : ℕ) : ℚ_[p])⁻¹‖ ≤ 1 := by rw [norm_inv, hd, inv_one]
  have hunit : C (((p - 2 * a : ℕ) : ℚ_[p])⁻¹) ∈ lifts (PadicInt.Coe.ringHom (p := p)) :=
    C_mem_lifts (PadicInt.Coe.ringHom (p := p)) ⟨_, hinv⟩
  convert mul_mem hunit hmem using 1
  rw [smul_eq_C_mul]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hd0 : ((p - 2 * a : ℕ) : ℚ_[p]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
  have hd' : ((p - 2 * a : ℕ) : ℚ_[p]) = p - 2 * a := by
    push_cast [show 2 * a ≤ p by omega]; ring
  have h1 : (((u₁ : ℚ) / (-(a : ℚ) ^ 2 + ((p - a : ℕ) : ℚ) ^ 2) : ℚ) : ℚ_[p]) =
      ((p - 2 * a : ℕ) : ℚ_[p])⁻¹ * (p : ℚ_[p])⁻¹ * ((u₁ : ℤ_[p]) : ℚ_[p]) := by
    have hden : (((-(a : ℚ) ^ 2 + ((p - a : ℕ) : ℚ) ^ 2) : ℚ) : ℚ_[p]) = p * (p - 2 * a) := by
      push_cast [show a ≤ p by omega]; ring
    rw [hd'] at hd0 ⊢
    rw [Rat.cast_div, hden, Rat.cast_intCast, PadicInt.coe_intCast]
    field_simp
  have h2 : (((u₂ : ℚ) / (-((p - a : ℕ) : ℚ) ^ 2 + (a : ℚ) ^ 2) : ℚ) : ℚ_[p]) =
      -(((p - 2 * a : ℕ) : ℚ_[p])⁻¹ * (p : ℚ_[p])⁻¹ * ((u₂ : ℤ_[p]) : ℚ_[p])) := by
    have hden : (((-((p - a : ℕ) : ℚ) ^ 2 + (a : ℚ) ^ 2) : ℚ) : ℚ_[p]) = -(p * (p - 2 * a)) := by
      push_cast [show a ≤ p by omega]; ring
    rw [hd'] at hd0 ⊢
    rw [Rat.cast_div, hden, Rat.cast_intCast, PadicInt.coe_intCast]
    field_simp
  rw [h1, h2]
  simp only [C_mul, C_neg]
  ring

end Zeta5Irr
