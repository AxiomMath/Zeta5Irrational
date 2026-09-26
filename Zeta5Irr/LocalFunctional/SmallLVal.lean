/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.SmallBinomInt
public import Zeta5Irr.LocalFunctional.SmallLBinom
public import Zeta5Irr.LocalFunctional.VpG
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# The valuation of the Bernoulli functional

Let `p` be a prime, `d ≥ 0`, `β ∈ ℤ`, and let `Q ∈ ℚ[x]` have degree at most `d` and satisfy
`Q(ℤ_p) ⊆ p^{-β} ℤ_p`. Then `v_p(L(Q)) ≥ -β - ⌊log_p(d + 1)⌋`, where `L` is the Bernoulli
functional `L(x ^ k) = B_k`.

The polynomial `p^β Q` maps `ℤ_p` into `ℤ_p`, so it is a `ℤ_p`-combination
`∑_{k ≤ d} b_k (x choose k)`. Extending `L` `ℚ_p`-linearly to `ℚ_p[x]` and using
`L (x choose k) = (-1)^k / (k + 1)`, we get `p^β L(Q) = ∑_{k ≤ d} b_k (-1)^k / (k + 1)`. Each
term has valuation at least `-v_p(k + 1) ≥ -⌊log_p(d + 1)⌋`, and hence so does the sum.

## Main results

* `Zeta5Irr.le_addValuation_bernoulliFunctional`: the bound
  `v_p(L(Q)) ≥ -β - ⌊log_p(d + 1)⌋`.
* `Zeta5Irr.lsum_bernoulli_map`: the `ℚ_p`-linear extension of `L` restricts to `L` on `ℚ[x]`.

## Implementation notes

Valuations are `Padic.addValuation`, valued in `WithTop ℤ`, so that `v_p(0) = ∞` and the
statement holds trivially when `L(Q) = 0`. The hypothesis `Q(ℤ_p) ⊆ p^{-β} ℤ_p` is stated as
`-β ≤ v_p(Q(x))` for every `x ∈ ℤ_p`. The `ℚ_p`-linear extension of `L` is written out as
`Polynomial.lsum` of the maps `a ↦ B_k a`, the same formula that defines `L` over `ℚ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

variable {p : ℕ} [Fact p.Prime]

/-- The `ℚ_p`-linear extension of the Bernoulli functional agrees with `L` on `ℚ[x]`. -/
theorem lsum_bernoulli_map (Q : ℚ[X]) :
    Polynomial.lsum (fun k => (bernoulli k : ℚ_[p]) • LinearMap.id (R := ℚ_[p]))
      (Q.map (algebraMap ℚ ℚ_[p])) = (bernoulliFunctional Q : ℚ_[p]) := by
  induction Q using Polynomial.induction_on' with
  | add P R hP hR => rw [Polynomial.map_add, map_add, hP, hR, map_add, Rat.cast_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, bernoulliFunctional_monomial, lsum_apply,
      sum_monomial_index _ _ (by simp)]
    simp [eq_ratCast, mul_comm]

/-- **The valuation of `L`.** If `Q ∈ ℚ[x]` has degree at most `d` and maps `ℤ_p` into
`p^{-β} ℤ_p`, then `v_p(L(Q)) ≥ -β - ⌊log_p(d + 1)⌋`. -/
@[zeta5irr "lem_small_L_val"]
theorem le_addValuation_bernoulliFunctional {d : ℕ} {β : ℤ} {Q : ℚ[X]} (hQ : Q.natDegree ≤ d)
    (hval : ∀ x : ℤ_[p], ((-β : ℤ) : WithTop ℤ) ≤ Padic.addValuation (aeval (x : ℚ_[p]) Q)) :
    ((-β - Nat.log p (d + 1) : ℤ) : WithTop ℤ) ≤
      Padic.addValuation (bernoulliFunctional Q : ℚ_[p]) := by
  set Lp : ℚ_[p][X] →ₗ[ℚ_[p]] ℚ_[p] :=
    Polynomial.lsum (fun k => (bernoulli k : ℚ_[p]) • LinearMap.id (R := ℚ_[p]))
  have hc := addValuation_prime_zpow (p := p) β
  set A := (p : ℚ_[p]) ^ β • Q.map (algebraMap ℚ ℚ_[p]) with hA
  have hdeg : A.natDegree ≤ d :=
    (natDegree_smul_le _ _).trans ((natDegree_map_le).trans hQ)
  have hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1 := by
    intro x
    rw [← zero_le_addValuation_iff_norm_le_one, hA, eval_smul, eval_map_algebraMap, smul_eq_mul,
      AddValuation.map_mul, hc]
    have := hval x
    generalize Padic.addValuation (aeval (x : ℚ_[p]) Q) = v at this ⊢
    induction v with
    | top => simp
    | coe v =>
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      rw [WithTop.coe_le_coe] at this
      omega
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_qbinom hdeg hint
  have hLA : Lp A = (p : ℚ_[p]) ^ β * (bernoulliFunctional Q : ℚ_[p]) := by
    rw [hA, map_smul, lsum_bernoulli_map, smul_eq_mul]
  have hsum : Lp A = ∑ k ∈ Finset.range (d + 1),
      (a k : ℚ_[p]) * (((-1) ^ k / (k + 1) : ℚ) : ℚ_[p]) := by
    rw [ha, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, lsum_bernoulli_map, bernoulliFunctional_qbinom, smul_eq_mul]
  have hterm : ∀ k ∈ Finset.range (d + 1), ((-(Nat.log p (d + 1) : ℤ) : ℤ) : WithTop ℤ) ≤
      Padic.addValuation ((a k : ℚ_[p]) * (((-1) ^ k / (k + 1) : ℚ) : ℚ_[p])) := by
    intro k hk
    have hk1 : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have hlog : padicValNat p (k + 1) ≤ Nat.log p (d + 1) :=
      (padicValNat_le_nat_log _).trans
        (Nat.log_mono_right (by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk))
    rw [AddValuation.map_mul]
    have ha0 : (0 : WithTop ℤ) ≤ Padic.addValuation (a k : ℚ_[p]) :=
      (zero_le_addValuation_iff_norm_le_one _).2 (a k).2
    have hb : Padic.addValuation (((-1) ^ k / (k + 1) : ℚ) : ℚ_[p]) =
        ((-(padicValNat p (k + 1) : ℤ) : ℤ) : WithTop ℤ) := by
      push_cast
      rw [div_eq_mul_inv, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_neg,
        AddValuation.map_one, nsmul_zero, zero_add,
        Padic.addValuation.apply (inv_ne_zero hk1), Padic.valuation_inv]
      norm_cast
      rw [Padic.valuation_natCast]
    rw [hb]
    calc ((-(Nat.log p (d + 1) : ℤ) : ℤ) : WithTop ℤ)
        = 0 + ((-(Nat.log p (d + 1) : ℤ) : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ _ := add_le_add ha0 (WithTop.coe_le_coe.2 (by omega))
  have key := AddValuation.map_le_sum Padic.addValuation hterm
  rw [← hsum, hLA, AddValuation.map_mul, hc] at key
  generalize Padic.addValuation (bernoulliFunctional Q : ℚ_[p]) = v at key ⊢
  induction v with
  | top => simp
  | coe v =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at key
    rw [WithTop.coe_le_coe]
    omega

end Zeta5Irr
