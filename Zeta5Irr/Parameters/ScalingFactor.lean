/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The scaling factor `S_K`

With `K = 40 n`, `N = 3 n` and `h = 37 n`, the scaling factor is the positive rational number
`S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)`.
It normalises the Hankel determinant `Δ_K`: the linear form of the construction is
`F_K = S_K Δ_K`.

## Main definitions

* `Zeta5Irr.scalingFactor`: the scaling factor `S_K`.

## Main results

* `Zeta5Irr.scalingFactor_pos`: `0 < S_K`.
* `Zeta5Irr.scalingFactor_ne_zero`: `S_K ≠ 0`.

## Implementation notes

* Since `K`, `N` and `h` are functions of `n`, so is `S_K`; it is indexed by `n` rather than
  by `K`.
* The exponent `h - 1` and the upper limit `h - 1` of the product are natural subtractions.
  For `n ≥ 1` they agree with the source; at `n = 0`, where `h = 0`, both are `0`, so the
  power of `4` and the product are `1` and `S_0 = 1`. No lemma about `S_K` needs `n ≥ 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Nat

/-- The scaling factor
`S_K = (K!)^{2h} 4^{h-1} / ((N!)^{12h} ∏_{i=1}^{h-1} ((2i)!)²)`, where `K = 40 n`, `N = 3 n`
and `h = 37 n`. The subtraction `h - 1` is truncated, which only matters at `n = 0`. -/
@[zeta5irr "def_SK"]
def scalingFactor (n : ℕ) : ℚ :=
  ((poleBound n)! : ℚ) ^ (2 * matrixOrder n) * 4 ^ (matrixOrder n - 1) /
    (((innerDegree n)! : ℚ) ^ (12 * matrixOrder n) *
      ∏ i ∈ Icc 1 (matrixOrder n - 1), (((2 * i)! : ℕ) : ℚ) ^ 2)

/-- The scaling factor is positive. -/
theorem scalingFactor_pos (n : ℕ) : 0 < scalingFactor n := by
  unfold scalingFactor
  have hprod : 0 < ∏ i ∈ Icc 1 (matrixOrder n - 1), (((2 * i)! : ℕ) : ℚ) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  positivity

/-- The scaling factor is nonzero. -/
theorem scalingFactor_ne_zero (n : ℕ) : scalingFactor n ≠ 0 :=
  (scalingFactor_pos n).ne'

end Zeta5Irr
