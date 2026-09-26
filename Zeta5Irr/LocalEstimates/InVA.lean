/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.MA

/-!
# The residue `v_A`

For a prime `p` and an integer `A ≥ 0`, the source sets `v_A = A - p m_A`, where
`m_A = ⌊A / p⌋`. Thus `v_A` is the least non-negative residue of `A` modulo `p`.

## Main definitions

* `Zeta5Irr.vA`: the residue `v_A = A mod p`.

## Main results

* `Zeta5Irr.vA_eq_sub`: `v_A = A - p m_A`, the defining formula of the source.
* `Zeta5Irr.mul_mA_add_vA`: `p m_A + v_A = A`.
* `Zeta5Irr.vA_lt`: `v_A < p` for `p > 0`.

## Implementation notes

* `v_A` is an `abbrev` for natural remainder `A % p`, so that Mathlib's lemmas about `Nat.mod`
  apply to it directly; `Zeta5Irr.vA_eq_sub` recovers the source's formula.
* The source takes `p` prime; primality is not needed to define `v_A`, so `p` is an arbitrary
  natural number here (with `A % 0 = A`, consistent with `m_A = A / 0 = 0`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

/-- The residue `v_A = A - p m_A`, the natural remainder of `A` modulo `p`. -/
@[zeta5irr "def_in_vA"]
abbrev vA (p A : ℕ) : ℕ :=
  A % p

/-- The division identity `p m_A + v_A = A`. -/
theorem mul_mA_add_vA (p A : ℕ) : p * mA p A + vA p A = A :=
  Nat.div_add_mod A p

/-- The source's defining formula `v_A = A - p m_A`. -/
theorem vA_eq_sub (p A : ℕ) : vA p A = A - p * mA p A :=
  Nat.mod_eq_sub_mul_div

/-- `v_A` is a residue: `v_A < p` whenever `p > 0`. -/
theorem vA_lt {p : ℕ} (hp : 0 < p) (A : ℕ) : vA p A < p :=
  Nat.mod_lt A hp

/-- `v_A` is congruent to `A` modulo `p`. -/
theorem vA_modEq (p A : ℕ) : vA p A ≡ A [MOD p] :=
  Nat.mod_modEq A p

end Zeta5Irr
