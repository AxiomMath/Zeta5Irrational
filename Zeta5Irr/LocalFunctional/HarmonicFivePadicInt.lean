/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# `H_m^{(5)}` is a `p`-adic integer for `m < p`

Let `p` be a prime and `m < p`. Every denominator `v` of `H_m^{(5)} = ∑_{v=1}^m v⁻⁵` satisfies
`1 ≤ v ≤ m < p`, so `p ∤ v`, `v` is a unit of `ℤ_p` and `v⁻⁵ ∈ ℤ_p`. Hence the finite sum
`H_m^{(5)}` lies in `ℤ_p`.

## Main results

* `Zeta5Irr.norm_harmonicFive_le_one`: `‖H_m^{(5)}‖_p ≤ 1` in `ℚ_p` for `m < p`.
* `Zeta5Irr.exists_padicInt_eq_harmonicFive`: `H_m^{(5)}` is the image of a `p`-adic integer.

## Implementation notes

Membership in `ℤ_p` is stated as `‖(H_m^{(5)} : ℚ_[p])‖ ≤ 1`, which is how Mathlib defines
`ℤ_[p]` as a subtype of `ℚ_[p]`; the literal form `∃ x : ℤ_[p], x = H_m^{(5)}` follows at once.
The hypothesis `0 ≤ m` of the source is automatic for `m : ℕ`. The proof uses the ultrametric
inequality for the finite sum and `‖v‖_p = 1` for `v` coprime to `p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (completion at a prime).
-/

@[expose] public section

open Finset

namespace Zeta5Irr

/-- For a prime `p` and `m < p`, the harmonic sum `H_m^{(5)}` lies in `ℤ_p`:
its `p`-adic norm is at most one. -/
@[zeta5irr "lem_local_harm_int"]
theorem norm_harmonicFive_le_one {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m < p) :
    ‖(harmonicFive m : ℚ_[p])‖ ≤ 1 := by
  rw [harmonicFive, Rat.cast_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun v hv => ?_
  obtain ⟨hv1, hvm⟩ := mem_Icc.1 hv
  have hcop : p.Coprime v := Nat.coprime_of_lt_prime (by omega) (by omega) Fact.out
  simp [norm_inv, norm_pow, Padic.norm_natCast_eq_one_iff.2 hcop]

/-- For a prime `p` and `m < p`, the harmonic sum `H_m^{(5)}` is the image of a `p`-adic
integer. -/
theorem exists_padicInt_eq_harmonicFive {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m < p) :
    ∃ x : ℤ_[p], (x : ℚ_[p]) = harmonicFive m :=
  ⟨⟨_, norm_harmonicFive_le_one hm⟩, rfl⟩

end Zeta5Irr
