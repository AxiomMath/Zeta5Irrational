/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDistSingle
public import Zeta5Irr.LocalFunctional.HarmonicFiveReflectIndex
public import Zeta5Irr.LocalFunctional.TauAnDiff
public import Zeta5Irr.LocalFunctional.TauFarShift

/-!
# The difference of the distributed functional at adjacent single poles

Let `p ≥ 5` be a prime and `r ∈ ℤ`. Moving a single pole from `r` to `r - 1` changes the
distributed functional by `-r⁻⁵`:
`𝒯_p(1; {r - 1}) - 𝒯_p(1; {r}) = -r⁻⁵`.

By the formula for a single pole, the difference is `p^{-5}` times a telescoping sum, which
collapses to `w_p(r - p) - w_p(r)`. If `p ∣ r`, with `ρ = r / p`, this is
`H_{d(ρ-1)}^{(5)} - H_{d(ρ)}^{(5)} = -ρ⁻⁵`. If `p ∤ r`, with `s = r / p ∈ ℚ_p`, it is
`τ^an(ε_s(z + 1)) - τ^an(ε_s)`, the coefficient `-s⁻⁵` of `z⁴` in `ε_s`. In both cases the
difference is `-(r / p)⁻⁵`, and multiplying by `p^{-5}` gives `-r⁻⁵`.

## Main results

* `Zeta5Irr.localPoleValue_sub_prime_sub`: `w_p(r - p) - w_p(r) = -(r / p)⁻⁵` for `p ≥ 5`.
* `Zeta5Irr.tauDist_singleton_sub_one_sub`: `𝒯_p(1; {r - 1}) - 𝒯_p(1; {r}) = -r⁻⁵`.

## Implementation notes

The source assumes `r ≠ 0`. The hypothesis is dropped here: at `r = 0` both sides vanish, the
right side because `0⁻¹ = 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p ≥ 5` and `r ∈ ℤ`, the local pole values at `r - p` and `r` differ by
`-(r / p)⁻⁵`. -/
theorem localPoleValue_sub_prime_sub (hp5 : 5 ≤ p) (r : ℤ) :
    localPoleValue p (r - p) - localPoleValue p r = -C ((((r : ℚ_[p]) / p) ^ 5)⁻¹) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases h : (p : ℤ) ∣ r
  · obtain ⟨ρ, rfl⟩ := h
    rw [show (p : ℤ) * ρ - p = p * (ρ - 1) by ring, localPoleValue_mul_left,
      localPoleValue_mul_left, sub_sub_sub_cancel_right, ← C_sub, ← Rat.cast_sub,
      harmonicFive_reflectIndex_sub_one_sub, ← C_neg]
    congr 1
    push_cast
    rw [mul_div_cancel_left₀ _ hp]
  · have h' : ¬(p : ℤ) ∣ r - p := fun h' => h (by simpa using h'.add (dvd_refl (p : ℤ)))
    set s : ℚ_[p] := (r : ℚ_[p]) / p with hs
    have hneg : s.valuation < 0 := by
      rw [hs, valuation_intCast_div_prime h]; exact neg_one_lt_zero
    rw [localPoleValue_of_not_dvd h', localPoleValue_of_not_dvd h, ← hs,
      show ((r - p : ℤ) : ℚ_[p]) / p = s - 1 by rw [hs]; push_cast; field_simp,
      ← tateSubst_one_one_farEps_of_valuation_neg hneg, ← C_sub,
      tauAn_tateSubst_one_one_sub hp5 (farEps_mem_tateAlgebra_and_tateNorm hneg).1,
      coeff_farEps, ← C_neg, inv_pow]

/-- **`𝒯_p(1; {r - 1}) - 𝒯_p(1; {r}) = -r⁻⁵`.** For a prime `p ≥ 5` and `r ∈ ℤ`, moving the
single pole of the distributed functional from `r` to `r - 1` changes it by `-r⁻⁵`. -/
@[zeta5irr "lem_tau_dist_diff"]
theorem tauDist_singleton_sub_one_sub (hp5 : 5 ≤ p) (r : ℤ) :
    tauDist p {r - 1} 1 - tauDist p {r} 1 = -C (((r : ℚ_[p]) ^ 5)⁻¹) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [tauDist_singleton_one, tauDist_singleton_one, ← smul_sub, ← Finset.sum_sub_distrib]
  have htel := Finset.sum_range_sub (fun a : ℕ => localPoleValue p (r - a)) p
  simp only [Nat.cast_succ, Nat.cast_zero, sub_zero] at htel
  rw [show ∑ a ∈ Finset.range p, (localPoleValue p (r - 1 - a) - localPoleValue p (r - a)) =
      ∑ a ∈ Finset.range p, (localPoleValue p (r - (a + 1)) - localPoleValue p (r - a)) from
    Finset.sum_congr rfl fun a _ => by rw [sub_sub, add_comm (1 : ℤ)],
    htel, localPoleValue_sub_prime_sub hp5, smul_neg, smul_C, smul_eq_mul]
  congr 2
  rw [div_pow, inv_div, ← div_eq_inv_mul, div_div_cancel_left' (pow_ne_zero 5 hp)]

end Zeta5Irr
