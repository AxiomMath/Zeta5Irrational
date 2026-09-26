/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Differences of squares of small indices are `p`-adic units

Let `p` be an odd prime and `0 ≤ c < c' ≤ m° = (p - 1) / 2`. Then `c'² - c²` is a unit of
`ℤ_p`. Indeed `c'² - c² = (c' - c)(c' + c)`, and both factors lie strictly between `0` and
`p`, so neither is divisible by `p`; a natural number not divisible by `p` is a unit of `ℤ_p`.

## Main results

* `Zeta5Irr.isUnit_natCast_padicInt_of_pos_of_lt`: a natural number `0 < n < p` is a unit
  of `ℤ_p`.
* `Zeta5Irr.isUnit_sq_sub_sq_of_lt_of_le_mStar`: for `c < c' ≤ m°`, `c'² - c²` is a unit of
  `ℤ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

namespace Zeta5Irr

/-- A natural number `n` with `0 < n < p` is a unit of `ℤ_[p]`. -/
theorem isUnit_natCast_padicInt_of_pos_of_lt {p : ℕ} [Fact p.Prime] {n : ℕ} (h0 : 0 < n)
    (hn : n < p) : IsUnit (n : ℤ_[p]) := by
  by_contra h
  rw [PadicInt.not_isUnit_iff, ← Int.cast_natCast, PadicInt.norm_intCast_lt_one_iff] at h
  exact absurd (Nat.le_of_dvd h0 (Int.natCast_dvd_natCast.mp h)) (by omega)

/-- For an odd prime `p` and `c < c' ≤ m° = (p - 1) / 2`, the difference of squares
`c'² - c²` is a unit of `ℤ_[p]`. -/
@[zeta5irr "lem_in_classes_coprime"]
theorem isUnit_sq_sub_sq_of_lt_of_le_mStar {p : ℕ} [Fact p.Prime] (hodd : Odd p) {c c' : ℕ}
    (hcc' : c < c') (hc' : c' ≤ mStar p) : IsUnit ((c' : ℤ_[p]) ^ 2 - (c : ℤ_[p]) ^ 2) := by
  have h2 := two_mul_mStar_add_one hodd
  have hadd := isUnit_natCast_padicInt_of_pos_of_lt (p := p) (n := c' + c) (by omega) (by omega)
  have hsub := isUnit_natCast_padicInt_of_pos_of_lt (p := p) (n := c' - c) (by omega) (by omega)
  push_cast [Nat.cast_sub hcc'.le] at hadd hsub
  rw [sq_sub_sq]
  exact hadd.mul hsub

end Zeta5Irr
