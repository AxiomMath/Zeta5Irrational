/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.EllA
public import Zeta5Irr.LimitingFunctions.EllXz
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Rat.Star

/-!
# `ℓ_A` as a value of `ℓ`

For a modulus `p`, a bound `A ≥ 0` and an integer `a` with `1 ≤ a ≤ (p - 1)/2`, the count
`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (mod p)}` is the value `ℓ(A/p, a/p)` of the function
`ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`. Since `p ∤ 2a`, the classes of `a` and `-a` are
distinct, and the two counts are `⌊(A - a)/p⌋ + 1` and `⌊(A + a)/p⌋`.

## Main results

* `Zeta5Irr.ellA_eq_card_filter_Ioc`: `ℓ_A(a)` counts integers in the interval `(0, A]`.
* `Zeta5Irr.ellA_eq_ell_div`: `ℓ_A(a) = ℓ(A/p, a/p)` for `0 < a` and `2a < p`.

## Implementation notes

* The source takes `p` prime and `A ≥ 1`. Neither is needed: the identity holds for every
  natural `p` and every `A ≥ 0` (for `A = 0` both sides vanish).
* For an integer `a` the condition `a ≤ (p - 1)/2` is stated as `2a < p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `1 ≤ a ≤ (p - 1)/2`, the count `ℓ_A(a)` equals `ℓ(A/p, a/p)`. -/
@[zeta5irr "lem_norm_ellA_scale"]
theorem ellA_eq_ell_div {p A : ℕ} {a : ℤ} (ha : 0 < a) (hap : 2 * a < p) :
    (ellA p A a : ℤ) = ell (A / p) (a / p) := by
  have hp : 0 < p := by omega
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  rw [ellA_eq_card_filter_Ioc, filter_or, card_union_of_disjoint]
  · push_cast
    rw [Int.Ioc_filter_modEq_card _ _ (by exact_mod_cast hp),
      Int.Ioc_filter_modEq_card _ _ (by exact_mod_cast hp)]
    simp only [Int.cast_natCast, Int.cast_zero, Int.cast_neg, zero_sub, sub_neg_eq_add,
      zero_add]
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have hap' : (2 * a : ℚ) < p := by exact_mod_cast hap
    have hA : (0 : ℚ) ≤ A := Nat.cast_nonneg A
    have h₁ : ⌊-(a : ℚ) / p⌋ = -1 := by
      rw [Int.floor_eq_iff, le_div_iff₀ hpq, div_lt_iff₀ hpq]
      constructor <;> push_cast <;> linarith
    have h₂ : ⌊(a : ℚ) / p⌋ = 0 := by
      rw [Int.floor_eq_iff, div_lt_iff₀ hpq]
      push_cast
      exact ⟨by positivity, by linarith⟩
    have h₃ : -1 ≤ ⌊((A : ℚ) - a) / p⌋ := by
      rw [← h₁]
      exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hpq.le)
    have h₄ : 0 ≤ ⌊((A : ℚ) + a) / p⌋ := by
      rw [← h₂]
      exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hpq.le)
    rw [h₁, h₂, max_eq_left (by omega), max_eq_left (by omega), ell_def]
    have e₁ : (A : ℝ) / p - a / p = ((((A : ℚ) - a) / p : ℚ) : ℝ) := by
      push_cast
      ring
    have e₂ : (A : ℝ) / p + a / p = ((((A : ℚ) + a) / p : ℚ) : ℝ) := by
      push_cast
      ring
    rw [e₁, e₂, Rat.floor_cast, Rat.floor_cast]
    ring
  · rw [disjoint_filter]
    intro j _ h₁ h₂
    have hd : (p : ℤ) ∣ 2 * a := by
      have := (h₁.symm.trans h₂).symm.dvd
      rwa [show a - -a = 2 * a by ring] at this
    have := Int.le_of_dvd (by omega) hd
    omega

end Zeta5Irr
