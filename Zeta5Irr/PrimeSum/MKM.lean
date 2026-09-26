/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.Lp

/-!
# The normalizing factor `m_{K,M}`

For an integer `M ≥ 40` and an integer `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, the normalizing
factor is
```
m_{K,M} = ∏_{p ≤ 2h} p ^ (-L_p(K, M)),
```
the product over the primes `p ≤ 2h`, where `K = 40 n`, `h = 37 n` and `L_p(K, M)` is the
local exponent. It is chosen so that `m_{K,M} F_K` has integer coefficients.

## Main definitions

* `Zeta5Irr.normalizingFactor`: the normalizing factor `m_{K,M}`.

## Main results

* `Zeta5Irr.normalizingFactor_pos`: `m_{K,M} > 0`.
* `Zeta5Irr.log_normalizingFactor`: `log m_{K,M} = -∑_{p ≤ 2h} L_p(K, M) log p`.
* `Zeta5Irr.normalizingFactor_eq_ratCast`: when the local exponents are integers `e p`,
  `m_{K,M}` is the rational number `∏_{p ≤ 2h} p ^ (-e p)`.

## Implementation notes

* As for the local exponent, the factor is indexed by `n`, `M`, with `K = 40 n`. The source's
  hypotheses on `K` and `M` are not needed to write the product down, so the definition is
  total.
* The local exponents are rational numbers; that they are integers, and hence that
  `m_{K,M}` is rational, is a separate result. The factor is therefore defined as a real
  number, with real powers `p ^ (-L_p(K, M))` of the positive reals `p`.
* The primes `p ≤ 2h` are `Nat.primesBelow (2 h + 1)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1 (The normalizing factor and integrality).
-/

@[expose] public section

namespace Zeta5Irr

/-- The normalizing factor `m_{K,M} = ∏_{p ≤ 2h} p ^ (-L_p(K, M))`, with `K = 40 n` and
`h = 37 n`, the product over the primes `p ≤ 2h`. -/
@[zeta5irr "def_mKM"]
noncomputable def normalizingFactor (n M : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow (2 * matrixOrder n + 1), (p : ℝ) ^ (-(localExponent n M p : ℝ))

variable {n M : ℕ}

/-- The normalizing factor `m_{K,M}` is positive. -/
theorem normalizingFactor_pos : 0 < normalizingFactor n M :=
  Finset.prod_pos fun _ hp =>
    Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.prime_of_mem_primesBelow hp).pos) _

/-- The logarithm of the normalizing factor: `log m_{K,M} = -∑_{p ≤ 2h} L_p(K, M) log p`. -/
theorem log_normalizingFactor :
    Real.log (normalizingFactor n M) =
      -∑ p ∈ Nat.primesBelow (2 * matrixOrder n + 1), (localExponent n M p : ℝ) * Real.log p := by
  rw [normalizingFactor, Real.log_prod fun p hp => (Real.rpow_pos_of_pos
    (Nat.cast_pos.2 (Nat.prime_of_mem_primesBelow hp).pos) _).ne', ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Real.log_rpow (Nat.cast_pos.2 (Nat.prime_of_mem_primesBelow hp).pos), neg_mul]

/-- If the local exponents at the primes `p ≤ 2h` are the integers `e p`, then `m_{K,M}` is
the rational number `∏_{p ≤ 2h} p ^ (-e p)`. -/
theorem normalizingFactor_eq_ratCast {e : ℕ → ℤ}
    (he : ∀ p ∈ Nat.primesBelow (2 * matrixOrder n + 1), localExponent n M p = e p) :
    normalizingFactor n M =
      ((∏ p ∈ Nat.primesBelow (2 * matrixOrder n + 1), (p : ℚ) ^ (-e p) : ℚ) : ℝ) := by
  rw [normalizingFactor, Rat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [he p hp, Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
  push_cast
  rfl

end Zeta5Irr
