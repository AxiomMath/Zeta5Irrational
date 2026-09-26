/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.OutForm0
public import Zeta5Irr.LocalEstimates.OutMomentInt
public import Zeta5Irr.LocalEstimates.OutUnimodular

/-!
# The outer range: the cross entries are integral

Let `p ≥ 7` be a prime, fix the parameters `N = 3 n` and `K = 40 n`, and let
`0 ≤ a, c ≤ m°` with `a ≠ c`. For all indices `i`, `j` the cross entry
`Φ₀(P_a q_{a,i}, P_c q_{c,j})` of the integral part of the outer form on the separating basis
lies in `ℤ_p[X]`.

Write `A = D_N ^ 5 P_a q_{a,i} P_c q_{c,j}` and `S = {N + 1, …, K}`, and divide `A` by the
monic pole product `D_S`, `A = P D_S + B`. Every `j' ∈ S` is `≡ ±e (mod p)` for exactly one
`0 ≤ e ≤ m°`; since `a ≠ c`, one of `e ≠ a`, `e ≠ c` holds, so `-j'²` is a root of `P_a` or of
`P_c`, and `A(-j'²) = 0`. The residue sum in `μ_{0,X}(A; S)` therefore vanishes and
`Φ₀(P_a q_{a,i}, P_c q_{c,j}) = μ₀(P)`. All the polynomials involved have integer
coefficients and `D_S` is monic, so `P ∈ ℤ[t]`; as `μ₀(t^e)` is `0` or a moment `μ(t^e)` with
`e < 2p - 3`, which lies in `ℤ_p`, the value `μ₀(P)` lies in `ℤ_p`.

## Main results

* `Zeta5Irr.norm_truncatedMomentFunctional_map_intCast_le_one`: `μ₀` maps `ℤ[t]` into `ℤ_p`.
* `Zeta5Irr.truncatedPoleFunctional_map_intCast_mem_lifts`: if `A ∈ ℤ[t]` vanishes at every
  `-j²`, `j ∈ S`, then `μ_{0,X}(A; S) ∈ ℤ_p[X]`.
* `Zeta5Irr.truncatedPoleFunctional_complClassFactor_mul_mem_lifts_of_ne`: for `a ≠ c` and
  `f, g ∈ ℤ[t]`, `μ_{0,X}(D_N⁵ (P_a f)(P_c g); {N + 1, …, K}) ∈ ℤ_p[X]`.
* `Zeta5Irr.outerIntegralForm_complClassFactor_mul_outerLocalPoly_mem_lifts`:
  `Φ₀(P_a q_{a,i}, P_c q_{c,j}) ∈ ℤ_p[X]` for `a ≠ c`.

## Implementation notes

* Membership in `ℤ_p[X]` is stated as membership in `Polynomial.lifts` of the inclusion
  `ℤ_p → ℚ_p`, and membership in `ℤ_p` as `‖x‖ ≤ 1`.
* Of the source's hypotheses only `p ≥ 7`, `0 ≤ a, c ≤ m°` and `a ≠ c` are used. The bounds
  `i < deg Q_a`, `j < deg Q_c` and the conditions `K ∈ 40 ℤ_{>0}`, `p ≤ K < 3 p`, `p² > 2 K`,
  `2 N < p`, `5 N ≤ 2 p - 2` are not needed, so the result is stated without them.
* The local polynomials `q_{a,i}` (`a ≥ 1`) and `q_{0,i}` are packaged as
  `Zeta5Irr.outerLocalPoly`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10: the outer range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p ≥ 7`, the truncated moment functional `μ₀` maps `ℤ[t]` into `ℤ_p`. -/
theorem norm_truncatedMomentFunctional_map_intCast_le_one (hp7 : 7 ≤ p) (f : ℤ[X]) :
    ‖truncatedMomentFunctional p (f.map (Int.castRingHom ℚ))‖ ≤ 1 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [Polynomial.map_add, map_add]
    exact (Padic.nonarchimedean _ _).trans (max_le hf hg)
  | monomial e c =>
    rw [map_monomial, truncatedMomentFunctional_monomial]
    split_ifs with he
    · rw [norm_mul]
      have hc : ‖((c : ℚ) : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p := p) c
      exact (mul_le_mul hc (norm_momentFunctional_X_pow_le_one hp7 he) (norm_nonneg _)
        zero_le_one).trans_eq (one_mul 1)
    · simp

/-- If `A ∈ ℤ[t]` vanishes at every `-j²` with `j ∈ S`, then for a prime `p ≥ 7` the integral
part `μ_{0,X}(A; S)` lies in `ℤ_p[X]`: it is the constant `μ₀(A /ₘ D_S)`, and `A /ₘ D_S` has
integer coefficients. -/
theorem truncatedPoleFunctional_map_intCast_mem_lifts (hp7 : 7 ≤ p) (S : Finset ℕ) (A : ℤ[X])
    (hA : ∀ j ∈ S, (A.map (Int.castRingHom ℚ)).eval (-((j : ℚ) ^ 2)) = 0) :
    truncatedPoleFunctional p S (A.map (Int.castRingHom ℚ)) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  rw [truncatedPoleFunctional_apply, sum_eq_zero fun j hj ↦ by rw [hA j hj, zero_div, zero_smul],
    add_zero, ← map_poleProduct S ℤ (Int.castRingHom ℚ),
    ← map_divByMonic _ (monic_poleProduct S ℤ)]
  exact C_mem_lifts (PadicInt.Coe.ringHom (p := p))
    ⟨_, norm_truncatedMomentFunctional_map_intCast_le_one hp7 _⟩

/-- For a prime `p ≥ 7` and `0 ≤ a, c ≤ m°` with `a ≠ c`, the integral part
`μ_{0,X}(D_N⁵ (P_a f)(P_c g); {N + 1, …, K})` lies in `ℤ_p[X]` for all `f, g ∈ ℤ[t]`: every
residue vanishes. -/
theorem truncatedPoleFunctional_complClassFactor_mul_mem_lifts_of_ne (hp7 : 7 ≤ p) {N K : ℕ}
    {a c : ℕ} (ha : a ≤ mStar p) (hc : c ≤ mStar p) (hac : a ≠ c) (f g : ℤ[X]) :
    truncatedPoleFunctional p (Icc (N + 1) K)
        ((poleProductRange N ℤ ^ 5 * (complClassFactor ℤ p (a : ℤ) N K * f) *
          (complClassFactor ℤ p (c : ℤ) N K * g)).map (Int.castRingHom ℚ)) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  refine truncatedPoleFunctional_map_intCast_mem_lifts hp7 _ _ fun k hk ↦ ?_
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_complClassFactor, eval_mul]
  by_cases hka : (k : ZMod p) = ((a : ℤ) : ZMod p) ∨ (k : ZMod p) = -((a : ℤ) : ZMod p)
  · have hkc : ¬((k : ZMod p) = ((c : ℤ) : ZMod p) ∨ (k : ZMod p) = -((c : ℤ) : ZMod p)) :=
      fun h ↦ hac (((natCast_eq_or_eq_neg_iff hodd ha k).mp hka).symm.trans
        ((natCast_eq_or_eq_neg_iff hodd hc k).mp h))
    rw [eval_neg_sq_complClassFactor hk hkc]
    ring
  · rw [eval_neg_sq_complClassFactor hk hka]
    ring

/-- **The cross entries of the outer range are integral.** For a prime `p ≥ 7`, indices
`0 ≤ a, c ≤ m°` with `a ≠ c`, and any `i`, `j`,
`Φ₀(P_a q_{a,i}, P_c q_{c,j}) ∈ ℤ_p[X]`. -/
@[zeta5irr "lem_out_cross_int"]
theorem outerIntegralForm_complClassFactor_mul_outerLocalPoly_mem_lifts (hp7 : 7 ≤ p)
    (n : ℕ) {a c : ℕ} (ha : a ≤ mStar p) (hc : c ≤ mStar p) (hac : a ≠ c) (i j : ℕ) :
    outerIntegralForm p n
        (complClassFactor ℚ p (a : ℤ) (innerDegree n) (poleBound n) *
          outerLocalPoly ℚ p (poleBound n) (a : ℤ) i)
        (complClassFactor ℚ p (c : ℤ) (innerDegree n) (poleBound n) *
          outerLocalPoly ℚ p (poleBound n) (c : ℤ) j) ∈
      lifts (PadicInt.Coe.ringHom (p := p)) := by
  have key := truncatedPoleFunctional_complClassFactor_mul_mem_lifts_of_ne hp7
    (N := innerDegree n) (K := poleBound n) ha hc hac (outerLocalPoly ℤ p (poleBound n) (a : ℤ) i)
    (outerLocalPoly ℤ p (poleBound n) (c : ℤ) j)
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_poleProductRange, map_complClassFactor,
    map_outerLocalPoly] at key
  exact key

end Zeta5Irr
