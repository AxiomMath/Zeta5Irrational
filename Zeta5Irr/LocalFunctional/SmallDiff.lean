/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom
public import Zeta5Irr.LocalFunctional.SmallBinomVal
public import Zeta5Irr.LocalFunctional.SmallBinomInt
public import Zeta5Irr.LocalFunctional.SmallVandermonde
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# The difference bound for integer-valued polynomials

Let `p` be a prime, `d ≥ 0`, and let `A ∈ ℚ_p[x]` have degree at most `d` and satisfy
`A(ℤ_p) ⊆ ℤ_p`. Then for all `x, y ∈ ℤ_p`,
`v_p(A(x) - A(y)) ≥ v_p(x - y) - ⌊log_p max(1, d)⌋`.

Write `A = ∑_{k ≤ d} a_k (x choose k)` with `a_k ∈ ℤ_p`, and `x = y + w`. By Vandermonde's
identity, `(y + w choose k) - (y choose k) = ∑_{j < k} (y choose j) (w choose (k - j))`. For
`1 ≤ m ≤ d` we have `m (w choose m) = w (w - 1 choose m - 1)`, and `(w - 1 choose m - 1) ∈ ℤ_p`,
so `v_p((w choose m)) ≥ v_p(w) - v_p(m) ≥ v_p(w) - ⌊log_p d⌋`. The ultrametric inequality
concludes.

## Main results

* `Zeta5Irr.natCast_mul_aeval_qbinom_succ`: `(m + 1) (w choose m + 1) = w (w - 1 choose m)`.
* `Zeta5Irr.norm_aeval_qbinom_le`: `‖(w choose m)‖ ≤ p^⌊log_p d⌋ ‖w‖` for `1 ≤ m ≤ d`.
* `Zeta5Irr.norm_aeval_qbinom_sub_le`: the difference bound for `(x choose k)`, `k ≤ d`.
* `Zeta5Irr.norm_eval_sub_eval_le`: `‖A(x) - A(y)‖ ≤ p^⌊log_p d⌋ ‖x - y‖`.
* `Zeta5Irr.addValuation_sub_le_addValuation_eval_sub`: the difference bound,
  `v_p(x - y) ≤ v_p(A(x) - A(y)) + ⌊log_p max(1, d)⌋`.

## Implementation notes

* The valuation is `Padic.addValuation`, valued in `ℤ ∪ {∞}`, so the cases `x = y` and
  `A(x) = A(y)` need no separate treatment. The source's subtraction of `⌊log_p max(1, d)⌋` from
  `v_p(x - y)` is written as its addition to `v_p(A(x) - A(y))`, which avoids subtraction in
  `ℤ ∪ {∞}`.
* `⌊log_p max(1, d)⌋` is `Nat.log p d`: Mathlib's `Nat.log p 0 = 0 = Nat.log p 1`, so the
  `max(1, ·)` is not needed.
* The estimate is proved first in the norm form `‖A(x) - A(y)‖ ≤ p^⌊log_p d⌋ ‖x - y‖`, from which
  the valuation form follows.
* The hypothesis `A(ℤ_p) ⊆ ℤ_p` is stated as `‖A(x)‖ ≤ 1` for `x ∈ ℤ_p`, as in
  `Zeta5Irr.exists_eq_sum_smul_qbinom`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Nat Finset

/-- `(m + 1) (x choose m + 1) = x ((x - 1) choose m)` in `ℚ[x]`. -/
theorem C_mul_qbinom_succ (m : ℕ) :
    C ((m + 1 : ℕ) : ℚ) * qbinom (m + 1) = X * (qbinom m).comp (X - 1) := by
  rw [qbinom, qbinom, descPochhammer_succ_left, smul_comp, ← C_mul', ← C_mul', ← mul_assoc,
    ← C_mul, mul_left_comm, factorial_succ]
  congr 3
  push_cast
  field_simp

/-- In a commutative `ℚ`-algebra, `(m + 1) (w choose m + 1) = w ((w - 1) choose m)`. -/
theorem natCast_mul_aeval_qbinom_succ {A : Type*} [CommRing A] [Algebra ℚ A] (m : ℕ) (w : A) :
    ((m + 1 : ℕ) : A) * aeval w (qbinom (m + 1)) = w * aeval (w - 1) (qbinom m) := by
  have h := congrArg (aeval w) (C_mul_qbinom_succ m)
  simpa [aeval_comp] using h

variable {p : ℕ} [Fact p.Prime]

/-- For `1 ≤ m ≤ d` and `w ∈ ℤ_p`, `‖(w choose m)‖ ≤ p^⌊log_p d⌋ ‖w‖`, that is,
`v_p((w choose m)) ≥ v_p(w) - ⌊log_p d⌋`. -/
theorem norm_aeval_qbinom_le {d m : ℕ} (hm : m ≠ 0) (hmd : m ≤ d) (w : ℤ_[p]) :
    ‖aeval (w : ℚ_[p]) (qbinom m)‖ ≤ (p : ℝ) ^ Nat.log p d * ‖w‖ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hm0 : ((m + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hnorm : (p : ℝ) ^ (-(Nat.log p d : ℤ)) ≤ ‖((m + 1 : ℕ) : ℚ_[p])‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation hm0, Padic.valuation_natCast,
      zpow_le_zpow_iff_right₀ hp, neg_le_neg_iff, Nat.cast_le]
    exact (padicValNat_le_nat_log _).trans (Nat.log_mono_right hmd)
  have h1 := congrArg norm (natCast_mul_aeval_qbinom_succ m (w : ℚ_[p]))
  rw [norm_mul, norm_mul] at h1
  have h2 : ‖aeval ((w : ℚ_[p]) - 1) (qbinom m)‖ ≤ 1 := by
    simpa using norm_aeval_qbinom_le_one (p := p) m (w - 1)
  have hpL : (0 : ℝ) < (p : ℝ) ^ Nat.log p d := by positivity
  have key : (p : ℝ) ^ (-(Nat.log p d : ℤ)) * ‖aeval (w : ℚ_[p]) (qbinom (m + 1))‖ ≤ ‖w‖ := by
    calc _ ≤ ‖((m + 1 : ℕ) : ℚ_[p])‖ * ‖aeval (w : ℚ_[p]) (qbinom (m + 1))‖ := by
          gcongr
      _ = _ := h1
      _ ≤ ‖(w : ℚ_[p])‖ * 1 := by gcongr
      _ = ‖w‖ := by simp
  rw [zpow_neg, zpow_natCast] at key
  rwa [inv_mul_le_iff₀ hpL] at key

/-- For `k ≤ d` and `x, y ∈ ℤ_p`,
`‖(x choose k) - (y choose k)‖ ≤ p^⌊log_p d⌋ ‖x - y‖`. -/
theorem norm_aeval_qbinom_sub_le {d k : ℕ} (hk : k ≤ d) (x y : ℤ_[p]) :
    ‖aeval (x : ℚ_[p]) (qbinom k) - aeval (y : ℚ_[p]) (qbinom k)‖ ≤
      (p : ℝ) ^ Nat.log p d * ‖x - y‖ := by
  have hx : (x : ℚ_[p]) = y + ((x - y : ℤ_[p]) : ℚ_[p]) := by push_cast; ring
  rw [hx, aeval_add_qbinom, sum_range_succ, Nat.sub_self, qbinom_zero, map_one, mul_one,
    add_sub_cancel_right]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j hj => ?_
  have hj := mem_range.mp hj
  rw [norm_mul]
  calc _ ≤ 1 * ((p : ℝ) ^ Nat.log p d * ‖x - y‖) := by
        gcongr
        · exact norm_aeval_qbinom_le_one j y
        · exact norm_aeval_qbinom_le (by omega) (by omega) _
    _ = _ := one_mul _

/-- **The difference bound**, norm form. If `A ∈ ℚ_p[x]` has degree at most `d` and
`A(ℤ_p) ⊆ ℤ_p`, then `‖A(x) - A(y)‖ ≤ p^⌊log_p d⌋ ‖x - y‖` for `x, y ∈ ℤ_p`. -/
theorem norm_eval_sub_eval_le {d : ℕ} {A : ℚ_[p][X]} (hA : A.natDegree ≤ d)
    (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) (x y : ℤ_[p]) :
    ‖A.eval (x : ℚ_[p]) - A.eval (y : ℚ_[p])‖ ≤ (p : ℝ) ^ Nat.log p d * ‖x - y‖ := by
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_qbinom hA hint
  simp only [ha, eval_finsetSum, eval_smul, eval_map_algebraMap, smul_eq_mul, ← sum_sub_distrib,
    ← mul_sub]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
  rw [norm_mul]
  calc _ ≤ 1 * ((p : ℝ) ^ Nat.log p d * ‖x - y‖) := by
        gcongr
        · exact (a k).2
        · exact norm_aeval_qbinom_sub_le (Nat.lt_succ_iff.mp (mem_range.mp hk)) x y
    _ = _ := one_mul _

/-- **The difference bound.** If `A ∈ ℚ_p[x]` has degree at most `d` and `A(ℤ_p) ⊆ ℤ_p`, then
`v_p(A(x) - A(y)) ≥ v_p(x - y) - ⌊log_p max(1, d)⌋` for `x, y ∈ ℤ_p`. -/
@[zeta5irr "lem_small_diff"]
theorem addValuation_sub_le_addValuation_eval_sub {d : ℕ} {A : ℚ_[p][X]} (hA : A.natDegree ≤ d)
    (hint : ∀ x : ℤ_[p], ‖A.eval (x : ℚ_[p])‖ ≤ 1) (x y : ℤ_[p]) :
    Padic.addValuation ((x : ℚ_[p]) - (y : ℚ_[p])) ≤
      Padic.addValuation (A.eval (x : ℚ_[p]) - A.eval (y : ℚ_[p])) + (Nat.log p d : ℤ) := by
  have h := norm_eval_sub_eval_le hA hint x y
  set D := A.eval (x : ℚ_[p]) - A.eval (y : ℚ_[p])
  rcases eq_or_ne D 0 with hD | hD
  · rw [hD, AddValuation.map_zero, WithTop.top_add]
    exact le_top
  have hw : (x : ℚ_[p]) - (y : ℚ_[p]) ≠ 0 := by
    rintro hw
    rw [PadicInt.norm_def, PadicInt.coe_sub, hw, norm_zero, mul_zero, norm_le_zero_iff] at h
    exact hD h
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.addValuation.apply hw, Padic.addValuation.apply hD, ← WithTop.coe_add,
    WithTop.coe_le_coe]
  rw [PadicInt.norm_def, PadicInt.coe_sub, Padic.norm_eq_zpow_neg_valuation hw,
    Padic.norm_eq_zpow_neg_valuation hD, ← zpow_natCast, ← zpow_add₀ (by positivity),
    zpow_le_zpow_iff_right₀ hp] at h
  omega

end Zeta5Irr
