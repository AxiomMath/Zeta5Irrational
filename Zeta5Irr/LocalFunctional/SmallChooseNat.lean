/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom

/-!
# Values of `(x choose k)` at natural numbers

For integers `m, k ≥ 0`, the value of the binomial polynomial `(x choose k)` at `x = m` is `0`
when `k > m`, and is the binomial coefficient `m! / (k! (m - k)!)` when `k ≤ m`.

Indeed the value is `(1 / k!) ∏_{i=0}^{k-1} (m - i)`. If `k > m` the factor with `i = m`
vanishes; if `k ≤ m` the product is `m! / (m - k)!`.

## Main results

* `Zeta5Irr.eval_natCast_qbinom_of_lt`: the value at `m` vanishes when `m < k`.
* `Zeta5Irr.eval_natCast_qbinom_of_le`: the value at `m` is `m! / (k! (m - k)!)` when `k ≤ m`.

## Implementation notes

Both statements are derived from `Zeta5Irr.eval_natCast_qbinom`, which identifies the value
with the natural-number binomial coefficient `m.choose k`; the two cases are then
`Nat.choose_eq_zero_of_lt` and `Nat.cast_choose`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (Small primes).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Nat

/-- For `m < k`, the value of `(x choose k)` at `x = m` is `0`. -/
@[zeta5irr "lem_small_choose_nat"]
theorem eval_natCast_qbinom_of_lt {m k : ℕ} (h : m < k) : (qbinom k).eval (m : ℚ) = 0 := by
  rw [eval_natCast_qbinom, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

/-- For `k ≤ m`, the value of `(x choose k)` at `x = m` is `m! / (k! (m - k)!)`. -/
@[zeta5irr "lem_small_choose_nat"]
theorem eval_natCast_qbinom_of_le {m k : ℕ} (h : k ≤ m) :
    (qbinom k).eval (m : ℚ) = (m ! : ℚ) / (k ! * (m - k)! : ℚ) := by
  rw [eval_natCast_qbinom, Nat.cast_choose ℚ h]

end Zeta5Irr
