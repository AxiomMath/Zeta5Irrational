/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.DegreePositivity.PartialFractions
public import Zeta5Irr.LocalEstimates.OutCrossInt
public import Zeta5Irr.LocalEstimates.OutQLower
public import Zeta5Irr.LocalEstimates.OutP
public import Zeta5Irr.LocalEstimates.OutClassSplit
public import Zeta5Irr.LocalEstimates.OutDivDiff

/-!
# The outer range: the diagonal entries with a high index are integral

Let `p ≥ 7` be a prime, fix the parameters `N = 3 n` and `K = 40 n` with `2 N < p ≤ K`, and
let `1 ≤ a ≤ m°`. If `max(i, j) ≥ ℓ_K(a) - 2`, then the entry
`Φ₀(P_a q_{a,i}, P_a q_{a,j})` of the integral part of the outer form on the separating basis
lies in `ℤ_p[X]`.

By symmetry of `Φ₀` we may take `i ≥ ℓ_K(a) - 2`, so that `q_{a,i} = Ξ_a q̃` with
`q̃ = (t + a²)^{i - ℓ_K(a) + 2}`. Put `S = {N + 1, …, K}` and let `T ⊆ S` be the set of
`j' ∈ S` with `j' < p` and `j' ≡ ±a (mod p)`. Then `D_S = D_T P_a Ξ_a`, and
`A = D_N ^ 5 P_a² q_{a,i} q_{a,j} = B̂ P_a Ξ_a` with `B̂ = D_N ^ 5 P_a q̃ q_{a,j} ∈ ℤ[t]`. At a
node `-j'²` with `j' ∈ S \ T` the factor `P_a Ξ_a` vanishes, and at a node with `j' ∈ T` the
residue is `A(-j'²) / D_S'(-j'²) = B̂(-j'²) / D_{T \ {j'}}(-j'²)`. Hence
`Φ₀ = μ₀(A /ₘ D_S) + ∑_{j' ∈ T} B̂(-j'²) / D_{T \ {j'}}(-j'²) · ν_{j'}(X)`, and the first
term lies in `ℤ_p` as for the cross entries. By the class split, `T = {p - a}` if `a ≤ N`, and
then the residue sum is the integer `B̂(-(p - a)²)` times `ν_{p - a}(X) ∈ ℤ_p[X]`. If `a > N`,
then `T = {a, p - a}` and the residue sum is
`(p - 2a)⁻¹ · (B̂(t₁) ν_a(X) - B̂(t₂) ν_{p-a}(X)) / p` with `t₁ = -a²`, `t₂ = -(p - a)²`; here
`p - 2a` is a `p`-adic unit, and `t₁ - t₂ = p (p - 2a)` divides `B̂(t₁) - B̂(t₂)`, so the
divided-difference lemma for the pole values applies.

## Main results

* `Zeta5Irr.truncatedPoleFunctional_eq_of_poleProduct_eq_mul`: if `D_S = D_T E` and `A = B E`
  with `T ⊆ S`, then the residue sum of `μ_{0,X}(A; S)` runs over `T` only, with residues
  `B(-j²) / D_{T \ {j}}(-j²)`.
* `Zeta5Irr.poleProduct_Icc_eq_mul_complClassFactor_mul_outXi`: `D_S = D_T P_a Ξ_a`.
* `Zeta5Irr.outerIntegralForm_complClassFactor_mul_outerBasis_mem_lifts`:
  `Φ₀(P_a q_{a,i}, P_a q_{a,j}) ∈ ℤ_p[X]` when `max(i, j) ≥ ℓ_K(a) - 2`.

## Implementation notes

* Membership in `ℤ_p[X]` is stated as membership in `Polynomial.lifts` of the inclusion
  `ℤ_p → ℚ_p`, and membership in `ℤ_p` as `‖x‖ ≤ 1`.
* Of the source's hypotheses only `p ≥ 7`, `p ≤ K`, `2 N < p`, `1 ≤ a ≤ m°` and
  `max(i, j) ≥ ℓ_K(a) - 2` are used. The conditions `K ∈ 40 ℤ_{>0}`, `K < 3 p`, `p² > 2 K`,
  `5 N ≤ 2 p - 2` and the bounds `i, j < ℓ_K(a) - δ_a` are not needed, so the result is stated
  without them. The threshold `max(i, j) ≥ ℓ_K(a) - 2` is read with truncated subtraction.
* The source's case distinction `δ_a = 1` / `δ_a = 0` appears as `a ≤ N` / `N < a`.
* Rather than computing `D_S'` at the surviving nodes from the explicit factorisation, the
  residues are compared through the product rule `D_S' = D_T' E + D_T E'`; that `E(-j²) ≠ 0`
  at a node of `T` then follows from `D_S'(-j²) ≠ 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10: the outer range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- If the pole product factors as `D_S = D_T E` with `T ⊆ S` and `A = B E`, then only the
nodes of `T` contribute to the residue sum of `μ_{0,X}(A; S)`, with residues
`A(-j²) / D_S'(-j²) = B(-j²) / D_{T \ {j}}(-j²)`. -/
theorem truncatedPoleFunctional_eq_of_poleProduct_eq_mul {S T : Finset ℕ} (hT : T ⊆ S)
    {A B E : ℚ[X]} (hD : poleProduct S ℚ = poleProduct T ℚ * E) (hA : A = B * E) :
    truncatedPoleFunctional p S A = C (truncatedMomentFunctional p (A /ₘ poleProduct S ℚ)) +
      ∑ j ∈ T, (B.eval (-((j : ℚ) ^ 2)) / (poleProduct (T.erase j) ℚ).eval (-((j : ℚ) ^ 2))) •
        (poleValue j).map (Rat.castHom ℚ_[p]) := by
  rw [truncatedPoleFunctional_apply, ← sum_subset hT]
  · congr 1
    refine sum_congr rfl fun j hj ↦ ?_
    have hS : j ∈ S := hT hj
    have hne := eval_derivative_poleProduct_ne_zero (K := ℚ) hS
    have hder : (derivative (poleProduct S ℚ)).eval (-((j : ℚ) ^ 2)) =
        (poleProduct (T.erase j) ℚ).eval (-((j : ℚ) ^ 2)) * E.eval (-((j : ℚ) ^ 2)) := by
      rw [hD, derivative_mul, eval_add, eval_mul, eval_mul, eval_derivative_poleProduct T hj,
        eval_neg_sq_poleProduct_of_mem hj, zero_mul, add_zero]
    rw [hder] at hne ⊢
    rw [hA, eval_mul, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)]
  · intro j hjS hjT
    have h0 : (poleProduct S ℚ).eval (-((j : ℚ) ^ 2)) = 0 :=
      eval_neg_sq_poleProduct_of_mem hjS
    have hTne : (poleProduct T ℚ).eval (-((j : ℚ) ^ 2)) ≠ 0 := by
      rw [← erase_eq_of_notMem hjT]
      exact eval_poleProduct_erase_ne_zero T j
    rw [hD, eval_mul] at h0
    rw [hA, eval_mul, (mul_eq_zero.1 h0).resolve_left hTne, mul_zero, zero_div, zero_smul]

/-- For `N < p` and `a ≢ 0 (mod p)`, the tail polynomial factors as
`D_{N+1..K} = D_T · P_a · Ξ_a`, where `T` is the set of `N < j ≤ K` with `j < p` and
`j ≡ ±a (mod p)`. -/
theorem poleProduct_Icc_eq_mul_complClassFactor_mul_outXi (R : Type*) [CommRing R]
    {p N K : ℕ} (hN : N < p) {a : ℤ} (ha : (a : ZMod p) ≠ 0) {T : Finset ℕ}
    (hT : ∀ j, j ∈ T ↔ j ∈ Icc (N + 1) K ∧ j < p ∧ ((j : ZMod p) = a ∨ (j : ZMod p) = -a)) :
    poleProduct (Icc (N + 1) K) R =
      poleProduct T R * (complClassFactor R p a N K * outXi R p K a) := by
  have hT' : ((Icc (N + 1) K).filter fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a).filter
      (fun j ↦ j < p) = T := by
    ext j
    rw [hT, filter_filter, mem_filter, and_comm (a := _ ∨ _)]
  have hX : ((Icc (N + 1) K).filter fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a).filter
      (fun j ↦ ¬j < p) =
      (Ioc p K).filter fun j : ℕ ↦ (j : ZMod p) = a ∨ (j : ZMod p) = -a := by
    ext j
    simp only [mem_filter, mem_Icc, mem_Ioc, not_lt]
    constructor
    · rintro ⟨⟨⟨-, hjK⟩, hc⟩, hpj⟩
      refine ⟨⟨lt_of_le_of_ne hpj ?_, hjK⟩, hc⟩
      rintro rfl
      rw [ZMod.natCast_self] at hc
      rcases hc with hc | hc
      · exact ha hc.symm
      · exact ha (neg_eq_zero.1 hc.symm)
    · rintro ⟨⟨hpj, hjK⟩, hc⟩
      exact ⟨⟨⟨by omega, hjK⟩, hc⟩, hpj.le⟩
  have hD : poleProduct (Icc (N + 1) K) R = dTail R N K := rfl
  rw [hD, ← prod_mul_complClassFactor, residuePoleProduct, residuePoleIndices,
    ← Finset.Icc_add_one_left_eq_Ioc, ← prod_filter_mul_prod_filter_not _ (fun j ↦ j < p), hT',
    hX, poleProduct, outXi]
  ring

/-- For `2 N < p ≤ K` and `1 ≤ a ≤ m°`, the indices `N < j ≤ K` with `j < p` and
`j ≡ ±a (mod p)` are the members of `{a, p - a}` exceeding `N`. -/
theorem mem_Icc_and_lt_and_class_iff {p N K a : ℕ} (hpK : p ≤ K) (ha : 1 ≤ a)
    (ham : a ≤ mStar p) (j : ℕ) :
    (j ∈ Icc (N + 1) K ∧ j < p ∧ ((j : ZMod p) = (a : ℤ) ∨ (j : ZMod p) = -(a : ℤ))) ↔
      N < j ∧ (j = a ∨ j = p - a) := by
  have h := congrArg (j ∈ ·) (filter_Icc_lt_class_eq hpK ha ham)
  simp only [mem_filter, mem_Icc, mem_insert, mem_singleton, eq_iff_iff] at h
  simp only [mem_Icc, Int.cast_natCast]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, h.1 ⟨⟨by omega, h2⟩, h3⟩⟩
  · rintro ⟨h1, h2⟩
    have := h.2 h2
    exact ⟨⟨by omega, this.1.2⟩, this.2⟩

/-- `Φ₀(P_a q_{a,i}, P_a q_{a,j}) ∈ ℤ_p[X]` when `i ≥ ℓ_K(a) - 2`, for every `j`. -/
theorem outerIntegralForm_complClassFactor_mul_outerBasis_mem_lifts_of_le (hp7 : 7 ≤ p)
    {n : ℕ} (hpK : p ≤ poleBound n)
    (hNp : 2 * innerDegree n < p) {a : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) {i : ℕ}
    (hi : ellA p (poleBound n) a - 2 ≤ i) (j : ℕ) :
    outerIntegralForm p n
        (complClassFactor ℚ p (a : ℤ) (innerDegree n) (poleBound n) *
          outerBasis ℚ p (poleBound n) (a : ℤ) i)
        (complClassFactor ℚ p (a : ℤ) (innerDegree n) (poleBound n) *
          outerBasis ℚ p (poleBound n) (a : ℤ) j) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  set N := innerDegree n
  set K := poleBound n
  have hp2 : p ≠ 2 := by omega
  have h2a : 2 * a < p := by rw [mStar_def] at ham; omega
  have ha0 : ((a : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ by have := Nat.le_of_dvd (by omega) h; omega
  let e := i + 2 - ellA p K a
  let Bz : ℤ[X] := poleProductRange N ℤ ^ 5 * complClassFactor ℤ p (a : ℤ) N K *
    (X + C ((a : ℤ) ^ 2)) ^ e * outerBasis ℤ p K (a : ℤ) j
  let Ez : ℤ[X] := complClassFactor ℤ p (a : ℤ) N K * outXi ℤ p K (a : ℤ)
  have hA : poleProductRange N ℚ ^ 5 *
      (complClassFactor ℚ p (a : ℤ) N K * outerBasis ℚ p K (a : ℤ) i) *
      (complClassFactor ℚ p (a : ℤ) N K * outerBasis ℚ p K (a : ℤ) j) =
      (Bz * Ez).map (Int.castRingHom ℚ) := by
    rw [outerBasis_of_le hi]
    simp only [Bz, Ez, e, Polynomial.map_mul, Polynomial.map_pow, map_poleProductRange,
      map_complClassFactor, map_outerBasis, map_outXi, Polynomial.map_add, map_X, map_C]
    simp
    ring
  have hBE : (Bz * Ez).map (Int.castRingHom ℚ) = Bz.map (Int.castRingHom ℚ) *
      (complClassFactor ℚ p (a : ℤ) N K * outXi ℚ p K (a : ℤ)) := by
    simp [Ez, Polynomial.map_mul, map_complClassFactor, map_outXi]
  have hmain (T : Finset ℕ) (hT : ∀ k, k ∈ T ↔ N < k ∧ (k = a ∨ k = p - a))
      (h : ∑ k ∈ T, ((Bz.map (Int.castRingHom ℚ)).eval (-((k : ℚ) ^ 2)) /
        (poleProduct (T.erase k) ℚ).eval (-((k : ℚ) ^ 2))) •
          (poleValue k).map (Rat.castHom ℚ_[p]) ∈ lifts (PadicInt.Coe.ringHom (p := p))) :
      outerIntegralForm p n
        (complClassFactor ℚ p (a : ℤ) N K * outerBasis ℚ p K (a : ℤ) i)
        (complClassFactor ℚ p (a : ℤ) N K * outerBasis ℚ p K (a : ℤ) j) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
    have hT' (k : ℕ) := (hT k).trans (mem_Icc_and_lt_and_class_iff (N := N) hpK ha ham k).symm
    have hD := poleProduct_Icc_eq_mul_complClassFactor_mul_outXi ℚ (K := K) (by omega : N < p)
      ha0 hT'
    unfold outerIntegralForm
    rw [hA, truncatedPoleFunctional_eq_of_poleProduct_eq_mul (fun k hk ↦ ((hT' k).1 hk).1) hD hBE]
    refine add_mem ?_ h
    rw [← map_poleProduct _ ℤ (Int.castRingHom ℚ), ← map_divByMonic _ (monic_poleProduct _ ℤ)]
    exact C_mem_lifts (PadicInt.Coe.ringHom (p := p))
      ⟨_, norm_truncatedMomentFunctional_map_intCast_le_one hp7 _⟩
  by_cases haN : a ≤ N
  · refine hmain {p - a} (fun k ↦ by rw [mem_singleton]; omega) ?_
    rw [sum_singleton, erase_singleton, poleProduct_empty, eval_one, div_one]
    exact eval_smul_poleValue_mem_lifts hp2 (by omega) Bz
  · exact hmain {a, p - a} (fun k ↦ by rw [mem_insert, mem_singleton]; omega)
      (sum_pair_div_smul_poleValue_mem_lifts hp2 ha h2a Bz)

/-- **The entries of the outer range with a high index are integral.** For a prime `p ≥ 7`
with `p ≤ K` and `2 N < p`, an index `1 ≤ a ≤ m°`, and `i`, `j` with
`max(i, j) ≥ ℓ_K(a) - 2`, `Φ₀(P_a q_{a,i}, P_a q_{a,j}) ∈ ℤ_p[X]`. -/
@[zeta5irr "lem_out_entry_int"]
theorem outerIntegralForm_complClassFactor_mul_outerBasis_mem_lifts (hp7 : 7 ≤ p) {n : ℕ}
    (hpK : p ≤ poleBound n) (hNp : 2 * innerDegree n < p) {a : ℕ} (ha : 1 ≤ a)
    (ham : a ≤ mStar p) {i j : ℕ} (hij : ellA p (poleBound n) a - 2 ≤ max i j) :
    outerIntegralForm p n
        (complClassFactor ℚ p (a : ℤ) (innerDegree n) (poleBound n) *
          outerBasis ℚ p (poleBound n) (a : ℤ) i)
        (complClassFactor ℚ p (a : ℤ) (innerDegree n) (poleBound n) *
          outerBasis ℚ p (poleBound n) (a : ℤ) j) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  rcases le_max_iff.1 hij with hi | hj
  · exact outerIntegralForm_complClassFactor_mul_outerBasis_mem_lifts_of_le hp7 hpK hNp ha ham
      hi j
  · rw [outerIntegralForm_comm]
    exact outerIntegralForm_complClassFactor_mul_outerBasis_mem_lifts_of_le hp7 hpK hNp ha ham
      hj i

end Zeta5Irr
