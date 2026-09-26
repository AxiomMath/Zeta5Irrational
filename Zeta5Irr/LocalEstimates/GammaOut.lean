/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.Rp
public import Zeta5Irr.LocalEstimates.OutTp

/-!
# The outer exponent `γ_p^out`

For a prime `p` with `p ≤ K < 3p`, the outer exponent is
```
γ_p^out = -7 (K - p) + 6 t_p - 1 - min(r_p, p - 1 - N + u)          if K < 2p,
γ_p^out = -7 (K - p) + 3 + 12 N + 5 t_p - min(r_p, p + u)           if K ≥ 2p,
```
where `r_p = max(0, K + 4N - 2p + 2)` is the outer rank bound, `u = max(0, N + v_K - p + 1)`
the overlap count and `t_p = min(N, v_K) + u` the small-class partial count, with
`v_K = K mod p`. It is the lower bound for the `p`-adic valuation of the Hankel determinant
`Δ_K` produced in the outer range: twice the total weight, minus the rank correction
`min(r_p, z)` where `z` is the number of vanishing weights.

## Main definitions

* `Zeta5Irr.outerExponent`: the outer exponent `γ_p^out`.

## Main results

* `Zeta5Irr.outerExponent_of_lt`: the formula for `γ_p^out` when `K < 2p`.
* `Zeta5Irr.outerExponent_of_le`: the formula for `γ_p^out` when `2p ≤ K`.

## Implementation notes

* The exponent is valued in `ℤ`, and every subtraction, including `K - p` and
  `p - 1 - N + u`, is read in `ℤ`; the natural-number quantities `r_p`, `u`, `t_p` are cast.
* The source defines `γ_p^out` only for a prime `p` with `p ≤ K < 3p`. Neither hypothesis is
  needed to write down the formula, so `p`, `N` and `K` are arbitrary natural numbers, and
  the case split is on `K < 2p` alone.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)),
  equation (4.14).
-/

@[expose] public section

namespace Zeta5Irr

/-- The outer exponent `γ_p^out`: for `K < 2p` it is
`-7 (K - p) + 6 t_p - 1 - min(r_p, p - 1 - N + u)`, and for `K ≥ 2p` it is
`-7 (K - p) + 3 + 12 N + 5 t_p - min(r_p, p + u)`. Here `r_p` is `Zeta5Irr.outerRankBound`,
`u` is `Zeta5Irr.overlapCount` and `t_p` is `Zeta5Irr.smallClassCount`; all arithmetic is
in `ℤ`. -/
@[zeta5irr "def_gamma_out"]
def outerExponent (p N K : ℕ) : ℤ :=
  if K < 2 * p then
    -7 * ((K : ℤ) - p) + 6 * smallClassCount p N K - 1 -
      min (outerRankBound K N p : ℤ) ((p : ℤ) - 1 - N + overlapCount p N K)
  else
    -7 * ((K : ℤ) - p) + 3 + 12 * N + 5 * smallClassCount p N K -
      min (outerRankBound K N p : ℤ) ((p : ℤ) + overlapCount p N K)

variable {p N K : ℕ}

/-- For `K < 2p`, `γ_p^out = -7 (K - p) + 6 t_p - 1 - min(r_p, p - 1 - N + u)`. -/
theorem outerExponent_of_lt (h : K < 2 * p) :
    outerExponent p N K = -7 * ((K : ℤ) - p) + 6 * smallClassCount p N K - 1 -
      min (outerRankBound K N p : ℤ) ((p : ℤ) - 1 - N + overlapCount p N K) :=
  ite_eq_left h

/-- For `2p ≤ K`, `γ_p^out = -7 (K - p) + 3 + 12 N + 5 t_p - min(r_p, p + u)`. -/
theorem outerExponent_of_le (h : 2 * p ≤ K) :
    outerExponent p N K = -7 * ((K : ℤ) - p) + 3 + 12 * N + 5 * smallClassCount p N K -
      min (outerRankBound K N p : ℤ) ((p : ℤ) + overlapCount p N K) :=
  ite_eq_right (Nat.not_lt.2 h)

end Zeta5Irr
