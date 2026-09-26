/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Mathlib.Tactic.ENatToNat

/-!
# The `p`-adic valuation of `H_m^{(5)}` for `m ≤ K`

Let `p` be a prime and `m ≤ K`. Every denominator `v` of `H_m^{(5)} = ∑_{v=1}^m v⁻⁵` satisfies
`p ^ {v_p(v)} ≤ v ≤ K`, so `v_p(v) ≤ ⌊log_p K⌋` and `v_p(v⁻⁵) = -5 v_p(v) ≥ -5 ⌊log_p K⌋`.
By the ultrametric inequality the finite sum `H_m^{(5)}` satisfies the same bound:
`v_p(H_m^{(5)}) ≥ -5 ⌊log_p K⌋`.

## Main results

* `Zeta5Irr.le_addValuation_harmonicFive`: `-5 ⌊log_p K⌋ ≤ v_p(H_m^{(5)})` for `m ≤ K`.

## Implementation notes

* The valuation is `Padic.addValuation` on `ℚ_p`, valued in `WithTop ℤ`, the valuation of the
  Gauss valuation `Zeta5Irr.vpG`; `H_m^{(5)}` is taken in `ℚ_p` through the cast `ℚ → ℚ_p`.
  For `m = 0` the sum is empty, its valuation is `⊤`, and the bound holds trivially.
* `⌊log_p K⌋` is `Nat.log p K`. The hypothesis `K ≥ 1` of the source is not needed: for
  `K = 0` also `m = 0`. The hypothesis `0 ≤ m` is automatic for `m : ℕ`.
* The ultrametric inequality for the finite sum is applied to the constants `v⁻⁵` directly,
  as `AddValuation.map_le_sum`, rather than through the Gauss valuation of constant
  polynomials.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

open Finset

namespace Zeta5Irr

/-- For a prime `p` and `m ≤ K`, the `p`-adic valuation of the harmonic sum `H_m^{(5)}` is at
least `-5 ⌊log_p K⌋`. -/
@[zeta5irr "lem_small_harm_val"]
theorem le_addValuation_harmonicFive {p : ℕ} [Fact p.Prime] {K m : ℕ} (hm : m ≤ K) :
    ((-5 * Nat.log p K : ℤ) : WithTop ℤ) ≤ Padic.addValuation (harmonicFive m : ℚ_[p]) := by
  rw [harmonicFive, Rat.cast_sum]
  refine AddValuation.map_le_sum _ fun v hv => ?_
  obtain ⟨hv1, hvm⟩ := mem_Icc.1 hv
  have hv0 : ((v : ℚ_[p]) ^ 5)⁻¹ ≠ 0 := by
    have : (v : ℚ_[p]) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
    positivity
  have hlog : padicValNat p v ≤ Nat.log p K :=
    (padicValNat_le_nat_log v).trans (Nat.log_mono_right (by omega))
  rw [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Padic.addValuation.apply hv0,
    Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_natCast, WithTop.coe_le_coe]
  omega

end Zeta5Irr
