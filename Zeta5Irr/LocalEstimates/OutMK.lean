/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.MA

/-!
# The quotient `m_K` in the outer range

If `p ≤ K < 3p` then `m_K = ⌊K / p⌋` lies in `{1, 2}`: from `p ≤ K` we get `K / p ≥ 1`, and
from `K < 3p` we get `K / p < 3`.

## Main results

* `Zeta5Irr.mA_eq_one_or_two`: if `p ≤ K < 3p` then `m_K = 1` or `m_K = 2`.
* `Zeta5Irr.mA_eq_one_of_lt_two_mul`, `Zeta5Irr.mA_eq_two_of_two_mul_le`: `m_K = 1` if
  `p ≤ K < 2p`, and `m_K = 2` if `2p ≤ K < 3p`.

## Implementation notes

* The source takes `p` prime. Primality is not needed: `K < 3p` already forces `p > 0`, and the
  bounds on `K / p` are then statements about natural division. The lemma is stated for
  arbitrary natural numbers `p` and `K`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.11 (The outer range: the counting behind (4.14)).
-/

@[expose] public section

namespace Zeta5Irr

/-- If `p ≤ K` then `1 ≤ m_K`. -/
theorem one_le_mA {p K : ℕ} (hp : 0 < p) (hpK : p ≤ K) : 1 ≤ mA p K :=
  (Nat.le_div_iff_mul_le hp).2 (by omega)

/-- If `K < 3p` then `m_K ≤ 2`. -/
theorem mA_le_two {p K : ℕ} (hK : K < 3 * p) : mA p K ≤ 2 :=
  Nat.le_of_lt_succ <| (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)

/-- If `p ≤ K < 3p` then `m_K = ⌊K / p⌋ ∈ {1, 2}`. -/
@[zeta5irr "lem_out_mK"]
theorem mA_eq_one_or_two {p K : ℕ} (hpK : p ≤ K) (hK : K < 3 * p) :
    mA p K = 1 ∨ mA p K = 2 := by
  have h1 := one_le_mA (by omega) hpK
  have h2 := mA_le_two hK
  omega

/-- If `p ≤ K < 2p` then `m_K = 1`. -/
theorem mA_eq_one_of_lt_two_mul {p K : ℕ} (hpK : p ≤ K) (hK : K < 2 * p) : mA p K = 1 :=
  le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
    (one_le_mA (by omega) hpK)

/-- If `2p ≤ K < 3p` then `m_K = 2`. -/
theorem mA_eq_two_of_two_mul_le {p K : ℕ} (hpK : 2 * p ≤ K) (hK : K < 3 * p) : mA p K = 2 :=
  le_antisymm (mA_le_two hK) ((Nat.le_div_iff_mul_le (by omega)).2 (by omega))

end Zeta5Irr
