/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Completion.Main

/-!
# `∑_{v ≥ 1} v⁻⁵` is irrational

The real number `ξ = ζ(5)` equals the convergent series `∑_{v ≥ 1} v⁻⁵`, and `ξ` is irrational.
Irrationality depends only on the value of a real number, so the series is irrational.

## Main results

* `Zeta5Irr.irrational_tsum_one_div_succ_pow_five`: `∑_{v ≥ 1} v⁻⁵` is irrational, with the
  sum indexed literally by `v = n + 1 ≥ 1`.
* `Zeta5Irr.irrational_tsum_one_div_nat_pow_five`: the same series summed over all `v : ℕ`.

## Implementation notes

In Lean `1 / (0 : ℝ) ^ 5 = 0`, so the series `∑' v : ℕ, 1 / (v : ℝ) ^ 5` over all natural
numbers has the same value as the series over `v ≥ 1`. Both forms are stated.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

namespace Zeta5Irr

/-- **`∑_{v ≥ 1} v⁻⁵` is irrational**, the sum written over all `v : ℕ`, where the `v = 0`
term `1 / 0 ^ 5` is `0`. -/
theorem irrational_tsum_one_div_nat_pow_five :
    Irrational (∑' v : ℕ, 1 / (v : ℝ) ^ 5) :=
  zetaFive_eq_tsum ▸ irrational_zetaFive

/-- **`∑_{v ≥ 1} v⁻⁵` is irrational**, the sum indexed literally by `v = n + 1 ≥ 1`. -/
@[zeta5irr "thm_tsum"]
theorem irrational_tsum_one_div_succ_pow_five :
    Irrational (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 5) := by
  have h := summable_one_div_nat_pow_five.tsum_eq_zero_add
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add] at h
  exact h ▸ irrational_tsum_one_div_nat_pow_five

end Zeta5Irr
