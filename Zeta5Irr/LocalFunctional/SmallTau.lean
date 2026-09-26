/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Tau
public import Zeta5Irr.LocalFunctional.SmallDeriv
public import Zeta5Irr.LocalFunctional.SmallLVal

/-!
# The valuation of `τ` at small primes

Let `p` be a prime, `d ≥ 0`, `β ∈ ℤ`, and let `P ∈ ℚ[x]` have degree at most `d` and satisfy
`P(ℤ_p) ⊆ p^{-β} ℤ_p`. Then `v_p(τ(P)) ≥ -β - 4 ⌊log_p(d + 1)⌋ - v_p(24)`.

Put `Q = P''' / 3!`, of degree at most `d`. The bound on divided derivatives gives
`Q(ℤ_p) ⊆ p^{-β - 3 ⌊log_p max(1, d)⌋} ℤ_p`, and the valuation bound for the Bernoulli
functional then gives `v_p(L(Q)) ≥ -β - 3 ⌊log_p max(1, d)⌋ - ⌊log_p(d + 1)⌋`. Since
`τ(P) = 6 L(Q) / 24`, `v_p(6) ≥ 0` and `⌊log_p max(1, d)⌋ ≤ ⌊log_p(d + 1)⌋`, the claim follows.

## Main results

* `Zeta5Irr.le_addValuation_tau`: `v_p(τ(P)) ≥ -β - 4 ⌊log_p(d + 1)⌋ - v_p(24)`.

## Implementation notes

As for the Bernoulli functional, valuations are `Padic.addValuation`, valued in `ℤ ∪ {∞}`, and
the hypothesis `P(ℤ_p) ⊆ p^{-β} ℤ_p` is `-β ≤ v_p(P(x))` for every `x ∈ ℤ_p`. The quantity
`v_p(24)` is `padicValNat p 24` and `⌊log_p(d + 1)⌋` is `Nat.log p (d + 1)`. The proof passes
through the equivalent norm form `‖τ(P)‖_p ≤ p^{β + 4 ⌊log_p(d + 1)⌋ + v_p(24)}`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

variable {p : ℕ} [Fact p.Prime]

/-- **The valuation of `τ` at small primes.** If `P ∈ ℚ[x]` has degree at most `d` and maps
`ℤ_p` into `p^{-β} ℤ_p`, then `v_p(τ(P)) ≥ -β - 4 ⌊log_p(d + 1)⌋ - v_p(24)`. -/
@[zeta5irr "lem_small_tau"]
theorem le_addValuation_tau {d : ℕ} {β : ℤ} {P : ℚ[X]} (hP : P.natDegree ≤ d)
    (hval : ∀ x : ℤ_[p], ((-β : ℤ) : WithTop ℤ) ≤ Padic.addValuation (aeval (x : ℚ_[p]) P)) :
    ((-β - 4 * Nat.log p (d + 1) - padicValNat p 24 : ℤ) : WithTop ℤ) ≤
      Padic.addValuation (tau P : ℚ_[p]) := by
  set Lm := Nat.log p (max 1 d)
  set Ld := Nat.log p (d + 1)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set A := P.map (algebraMap ℚ ℚ_[p])
  have hA : A.natDegree ≤ d := natDegree_map_le.trans hP
  have hbd : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ (p : ℝ) ^ β := fun x => by
    have := intCast_le_padicAddValuation_iff.1 (hval x)
    rwa [neg_neg, ← eval_map_algebraMap] at this
  set Q : ℚ[X] := C (1 / 6 : ℚ) * derivative^[3] P with hQ
  have hQdeg : Q.natDegree ≤ d :=
    (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative _ _).trans (by omega))
  have hvalQ : ∀ x : ℤ_[p], ((-(β + 3 * Lm) : ℤ) : WithTop ℤ) ≤
      Padic.addValuation (aeval (x : ℚ_[p]) Q) := fun x => by
    rw [intCast_le_padicAddValuation_iff, neg_neg]
    have := norm_eval_iterate_derivative_div_factorial_le 3 hA hbd x
    convert this using 2
    have h3 : aeval (x : ℚ_[p]) (derivative^[3] P) = (derivative^[3] A).eval (x : ℚ_[p]) := by
      rw [← eval_map_algebraMap, iterate_derivative_map]
    rw [hQ, map_mul, aeval_C, h3]
    simp [Nat.factorial, div_eq_inv_mul]
  have hLQ := intCast_le_padicAddValuation_iff.1 (le_addValuation_bernoulliFunctional hQdeg hvalQ)
  rw [neg_sub, sub_neg_eq_add] at hLQ
  have htau : (tau P : ℚ_[p]) = (bernoulliFunctional Q : ℚ_[p]) * 6 * ((24 : ℕ) : ℚ_[p])⁻¹ := by
    have : derivative^[3] P = (6 : ℚ) • Q := by
      rw [hQ, smul_eq_C_mul, ← mul_assoc, ← C_mul]; norm_num
    rw [tau_apply, this, map_smul, smul_eq_mul]
    push_cast
    ring
  rw [intCast_le_padicAddValuation_iff, htau, norm_mul, norm_mul, norm_natCast_inv_eq_zpow
    (by norm_num)]
  have h6 : ‖(6 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) 6
  calc _ ≤ (p : ℝ) ^ (Ld + (β + 3 * Lm)) * 1 * (p : ℝ) ^ padicValNat p 24 := by gcongr
    _ ≤ (p : ℝ) ^ (Ld + (β + 3 * Lm)) * (p : ℝ) ^ (padicValNat p 24 : ℤ) := by
        rw [mul_one, zpow_natCast]
    _ ≤ _ := by
        rw [← zpow_add₀ hp0.ne']
        refine zpow_le_zpow_right₀ hp1 ?_
        have : Lm ≤ Ld := Nat.log_mono_right (by omega)
        omega

end Zeta5Irr
