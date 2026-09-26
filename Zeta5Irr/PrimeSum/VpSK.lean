/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.ScalingFactor
public import Mathlib.Tactic.ENatToNat

/-!
# The `p`-adic valuation of the scaling factor `S_K`

For a prime `p`, the `p`-adic valuation of the scaling factor
`S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)` is read off from
Legendre's formula `v_p(m!) = ∑_{a ≥ 1} ⌊m / p^a⌋`:
`v_p(S_K) = 2h ∑_{a≥1} ⌊K/p^a⌋ - 12h ∑_{a≥1} ⌊N/p^a⌋ - 2 ∑_{i=1}^{h-1} ∑_{a≥1} ⌊2i/p^a⌋
  + (h-1) v_p(4)`.

## Main results

* `Zeta5Irr.padicValNat_factorial_eq_finsum`: Legendre's formula with the sum over all
  `a ≥ 1`, written as a `finsum`.
* `Zeta5Irr.padicValRat_scalingFactor`: the formula for `v_p(S_K)`.

## Implementation notes

* The sums over all `a ≥ 1` are `finsum`s over `Set.Ici 1`; only finitely many terms are
  nonzero. Mathlib's `padicValNat_factorial` states Legendre's formula as a sum over
  `Finset.Ico 1 b` for any `b > log_p m`, and `padicValNat_factorial_eq_finsum` converts.
* As in the definition of `S_K`, `h - 1` is a truncated subtraction. The formula holds for
  every `n`, including `n = 0` where both sides vanish, so no hypothesis `n ≥ 1` is needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1: the normalizing factor and integrality.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Nat

/-- **Legendre's formula** with the sum taken over all `a ≥ 1`:
`v_p(m!) = ∑_{a ≥ 1} ⌊m / p^a⌋`. -/
theorem padicValNat_factorial_eq_finsum {p : ℕ} [hp : Fact p.Prime] (m : ℕ) :
    padicValNat p m ! = ∑ᶠ a ∈ Set.Ici 1, m / p ^ a := by
  rw [padicValNat_factorial (b := Nat.log p m + 1) (Nat.lt_succ_self _)]
  symm
  apply finsum_mem_eq_sum_of_subset
  · rintro a ⟨ha1, ha⟩
    simp only [Function.mem_support, ne_eq, Nat.div_eq_zero_iff, not_or, not_lt] at ha
    simp only [coe_Ico, Set.mem_Ico]
    refine ⟨ha1, Nat.lt_succ_of_le ?_⟩
    exact Nat.le_log_of_pow_le hp.out.one_lt ha.2
  · intro a ha
    simp only [coe_Ico, Set.mem_Ico] at ha
    exact ha.1

/-- The `p`-adic valuation of the scaling factor `S_K`, for `K = 40 n`, `N = 3 n` and
`h = 37 n`:
`v_p(S_K) = 2h ∑_{a≥1} ⌊K/p^a⌋ - 12h ∑_{a≥1} ⌊N/p^a⌋ - 2 ∑_{i=1}^{h-1} ∑_{a≥1} ⌊2i/p^a⌋
  + (h-1) v_p(4)`. -/
@[zeta5irr "lem_vp_SK"]
theorem padicValRat_scalingFactor (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    padicValRat p (scalingFactor n) =
      2 * matrixOrder n * (∑ᶠ a ∈ Set.Ici 1, poleBound n / p ^ a : ℕ) -
        12 * matrixOrder n * (∑ᶠ a ∈ Set.Ici 1, innerDegree n / p ^ a : ℕ) -
        2 * ∑ i ∈ Icc 1 (matrixOrder n - 1), (∑ᶠ a ∈ Set.Ici 1, 2 * i / p ^ a : ℕ) +
        (matrixOrder n - 1 : ℕ) * padicValNat p 4 := by
  simp only [← padicValNat_factorial_eq_finsum]
  set h := matrixOrder n
  have hA : ((poleBound n)! : ℚ) ^ (2 * h) * 4 ^ (h - 1) =
      (((poleBound n)! ^ (2 * h) * 4 ^ (h - 1) : ℕ) : ℚ) := by push_cast; rfl
  have hB : ((innerDegree n)! : ℚ) ^ (12 * h) *
      ∏ i ∈ Icc 1 (h - 1), (((2 * i)! : ℕ) : ℚ) ^ 2 =
      (((innerDegree n)! ^ (12 * h) * ∏ i ∈ Icc 1 (h - 1), ((2 * i)!) ^ 2 : ℕ) : ℚ) := by
    push_cast; rfl
  have hprod : ∏ i ∈ Icc 1 (h - 1), ((2 * i)!) ^ 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (factorial_ne_zero _)
  have hvprod : padicValNat p (∏ i ∈ Icc 1 (h - 1), ((2 * i)!) ^ 2) =
      ∑ i ∈ Icc 1 (h - 1), 2 * padicValNat p (2 * i)! := by
    induction Icc 1 (h - 1) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [prod_insert hj, sum_insert hj, padicValNat.mul (pow_ne_zero _ (factorial_ne_zero _))
        (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (factorial_ne_zero _)),
        padicValNat.pow, ih]
  have hBne : (innerDegree n)! ^ (12 * h) * ∏ i ∈ Icc 1 (h - 1), ((2 * i)!) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (factorial_ne_zero _)) hprod
  unfold scalingFactor
  rw [hA, hB, padicValRat.div (by positivity) (by exact_mod_cast hBne),
    padicValRat.of_nat, padicValRat.of_nat,
    padicValNat.mul (pow_ne_zero _ (factorial_ne_zero _)) (by positivity),
    padicValNat.mul (pow_ne_zero _ (factorial_ne_zero _)) hprod,
    padicValNat.pow, padicValNat.pow, padicValNat.pow, hvprod]
  push_cast
  rw [Finset.mul_sum]
  ring

end Zeta5Irr
