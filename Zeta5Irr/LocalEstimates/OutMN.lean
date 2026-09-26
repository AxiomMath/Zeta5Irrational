/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.MA
public import Zeta5Irr.Parameters.Basic

/-!
# The quotient `m_N` vanishes in the outer range

In the outer range the prime `p` satisfies `2N < p`. Then `N < p`, so `m_N = ⌊N / p⌋ = 0`.

## Main results

* `Zeta5Irr.mA_eq_zero_of_two_mul_lt`: if `2N < p` then `m_N = 0`.
* `Zeta5Irr.mA_innerDegree_eq_zero`: the same for `N = 3n`.

## Implementation notes

* The source takes `p` an odd prime and `N ≥ 0`; neither hypothesis is needed, since `N` is a
  natural number and `N < p` already forces `N / p = 0`. The lemma is stated for arbitrary
  natural numbers `p` and `N`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8 (The outer range: the separating basis).
-/

@[expose] public section

namespace Zeta5Irr

/-- If `2N < p` then `m_N = ⌊N / p⌋ = 0`. -/
@[zeta5irr "lem_out_mN"]
theorem mA_eq_zero_of_two_mul_lt {p N : ℕ} (h : 2 * N < p) : mA p N = 0 :=
  Nat.div_eq_of_lt (by omega)

/-- In the outer range `2N < p`, with `N = 3n`, the quotient `m_N` vanishes. -/
theorem mA_innerDegree_eq_zero {p n : ℕ} (h : 2 * innerDegree n < p) :
    mA p (innerDegree n) = 0 :=
  mA_eq_zero_of_two_mul_lt h

end Zeta5Irr
