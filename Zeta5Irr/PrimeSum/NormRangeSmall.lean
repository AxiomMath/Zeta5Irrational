/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.Lp
public import Mathlib.Algebra.Order.Star.Real

/-!
# The small primes are negligible in the normalizing factor

Let `K = 40 n`, `h = 37 n` and let `M` be an integer with `K ≥ 200 M²`. For every prime
`p ≤ √(5K)` one has `p M ≤ K`, so the local exponent is
`L_p(K, M) = -6 h ⌊log_p (5K)⌋ - h v_p(24)`. Since `v_p(24) ≤ ⌊log_p 24⌋ ≤ ⌊log_p (5K)⌋` and
`⌊log_p (5K)⌋ log p ≤ log (5K)`, each term `|L_p(K, M) log p|` is at most `7 h log (5K)`, and
there are at most `√(5K)` such primes, so
```
|∑_{p ≤ √(5K)} L_p(K, M) log p| ≤ 7 h √(5K) log (5K) ≤ 15 K^{3/2} log (5K).
```

## Main results

* `Zeta5Irr.abs_sum_localExponent_mul_log_le`: the bound
  `|∑_{p ≤ √(5K)} L_p(K, M) log p| ≤ 15 K^{3/2} log (5K)`.

## Implementation notes

* The primes `p ≤ √(5K)` are those `p ≤ Nat.sqrt (5K)`, the integer square root.
* The source assumes `M ≥ 40` and `K ≥ 200 M²`. Only `5 M² ≤ K` is used, which is what makes
  `p M ≤ K` for every `p ≤ √(5K)`; the result is stated under that weaker hypothesis.
* The source bounds the two summands of `-L_p(K, M)` separately; here the second one is
  absorbed into the first via `v_p(24) ≤ ⌊log_p (5K)⌋`, which uses `h = (37/40) K` rather than
  `h ≤ K`. The resulting constant `7 · (37/40) · √5 < 15` is the same.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.8 (The growth of the normalizing factor).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- Each prime `p ≤ √(5K)` contributes at most `7 h log (5K)` to the small-prime sum. -/
theorem abs_localExponent_mul_log_le {n M p : ℕ} (hK : 5 * M ^ 2 ≤ poleBound n)
    (hpp : p.Prime) (hps : p ≤ Nat.sqrt (5 * poleBound n)) :
    |(localExponent n M p : ℝ) * Real.log p| ≤
      7 * matrixOrder n * Real.log (5 * poleBound n) := by
  set K := poleBound n
  have hps' : p * p ≤ 5 * K := Nat.le_sqrt.1 hps
  have hpM : p * M ≤ K := by
    have h1 : (p * M) ^ 2 ≤ K ^ 2 := by
      have : 5 * (p * M) ^ 2 ≤ 5 * K * K := by
        calc 5 * (p * M) ^ 2 = (p * p) * (5 * M ^ 2) := by ring
          _ ≤ (5 * K) * K := Nat.mul_le_mul hps' hK
      nlinarith
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h1
  have hK0 : 0 < K := by
    have := hpp.two_le
    nlinarith
  have h24 : 24 ≤ 5 * K := by
    obtain ⟨c, hc⟩ := forty_dvd_poleBound n
    omega
  set a := Nat.log p (5 * K)
  have hb : padicValNat p 24 ≤ a := by
    have hdvd : p ^ padicValNat p 24 ≤ 5 * K :=
      (Nat.le_of_dvd (by norm_num) pow_padicValNat_dvd).trans h24
    exact Nat.le_log_of_pow_le hpp.one_lt hdvd
  have ha : (a : ℝ) * Real.log p ≤ Real.log (5 * K) := by
    have hpow : p ^ a ≤ 5 * K := Nat.pow_log_le_self p (by omega)
    have : ((p : ℝ) ^ a) ≤ ((5 * K : ℕ) : ℝ) := by exact_mod_cast hpow
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [← Real.log_pow]
    calc Real.log ((p : ℝ) ^ a) ≤ Real.log ((5 * K : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) this
      _ = Real.log (5 * K) := by push_cast; rfl
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [localExponent_of_mul_le_natLog hpM]
  have hb' : (padicValNat p 24 : ℝ) ≤ a := by exact_mod_cast hb
  have hh : (0 : ℝ) ≤ matrixOrder n := Nat.cast_nonneg _
  push_cast
  rw [abs_of_nonpos (by
    have : (0 : ℝ) ≤ (padicValNat p 24 : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hh this, mul_nonneg hh (Nat.cast_nonneg (α := ℝ) a)])]
  have hab : ((6 * matrixOrder n * a + matrixOrder n * padicValNat p 24 : ℝ)) * Real.log p ≤
      7 * matrixOrder n * (a * Real.log p) := by
    nlinarith [mul_le_mul_of_nonneg_left hb' hh]
  nlinarith [mul_le_mul_of_nonneg_left ha (by positivity : (0 : ℝ) ≤ 7 * matrixOrder n)]

/-- **The small primes are negligible.** If `5 M² ≤ K = 40 n` (in particular if `M ≥ 40` and
`K ≥ 200 M²`), then `|∑_{p ≤ √(5K)} L_p(K, M) log p| ≤ 15 K^{3/2} log (5K)`, the sum being
over primes. -/
@[zeta5irr "lem_norm_range_small"]
theorem abs_sum_localExponent_mul_log_le {n M : ℕ} (hK : 5 * M ^ 2 ≤ poleBound n) :
    |∑ p ∈ (Iic (Nat.sqrt (5 * poleBound n))).filter Nat.Prime,
        (localExponent n M p : ℝ) * Real.log p| ≤
      15 * (poleBound n : ℝ) ^ (3 / 2 : ℝ) * Real.log (5 * poleBound n) := by
  set K := poleBound n with hKdef
  set s := Nat.sqrt (5 * K)
  set S := (Iic s).filter Nat.Prime
  have hlogK : 0 ≤ Real.log (5 * K) := by exact_mod_cast Real.log_natCast_nonneg (5 * K)
  have hterm : ∀ p ∈ S, |(localExponent n M p : ℝ) * Real.log p| ≤
      7 * matrixOrder n * Real.log (5 * K) := fun p hp =>
    abs_localExponent_mul_log_le hK (mem_filter.1 hp).2 (mem_Iic.1 (mem_filter.1 hp).1)
  have hcard : (S.card : ℝ) ≤ Real.sqrt (5 * K) := by
    have h1 : S.card ≤ s := by
      calc S.card ≤ (Icc 1 s).card := card_le_card fun p hp => by
            obtain ⟨hps, hpp⟩ := mem_filter.1 hp
            exact mem_Icc.2 ⟨hpp.one_lt.le, mem_Iic.1 hps⟩
        _ = s := by simp
    calc (S.card : ℝ) ≤ s := by exact_mod_cast h1
      _ ≤ Real.sqrt ((5 * K : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ = Real.sqrt (5 * K) := by push_cast; rfl
  calc |∑ p ∈ S, (localExponent n M p : ℝ) * Real.log p|
      ≤ ∑ p ∈ S, |(localExponent n M p : ℝ) * Real.log p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, 7 * matrixOrder n * Real.log (5 * K) := sum_le_sum hterm
    _ = S.card * (7 * matrixOrder n * Real.log (5 * K)) := by simp
    _ ≤ Real.sqrt (5 * K) * (7 * matrixOrder n * Real.log (5 * K)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 15 * (K : ℝ) ^ (3 / 2 : ℝ) * Real.log (5 * K) := by
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        have hsq : Real.sqrt (5 * K) = Real.sqrt 5 * Real.sqrt K :=
          Real.sqrt_mul (by norm_num) _
        have hpow : (K : ℝ) ^ (3 / 2 : ℝ) = K * Real.sqrt K := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hK0 (by norm_num),
            Real.rpow_one, Real.sqrt_eq_rpow]
        have h5 : Real.sqrt 5 ≤ 9 / 4 := by
          rw [Real.sqrt_le_left (by norm_num)]
          norm_num
        have hh : (matrixOrder n : ℝ) = 37 / 40 * K := by
          simp only [hKdef, matrixOrder, poleBound]
          push_cast
          ring
        rw [hsq, hpow, hh]
        have hsK : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
        have : 0 ≤ (K : ℝ) * Real.sqrt K * Real.log (5 * K) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h5 this]

end Zeta5Irr
