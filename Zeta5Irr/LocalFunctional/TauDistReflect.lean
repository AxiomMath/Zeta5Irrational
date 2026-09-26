/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDistSingle
public import Zeta5Irr.LocalFunctional.TauAnReflect
public import Zeta5Irr.LocalFunctional.TauFarReflect

/-!
# Reflection symmetry of the distributed functional of a single pole

Let `p ≥ 5` be a prime and `r ∈ ℤ`. The distributed functional of a single pole is invariant
under the reflection `r ↦ -1 - r`: `𝒯_p(1; {-1 - r}) = 𝒯_p(1; {r})`.

The key step is the symmetry `w_p(-m - p) = w_p(m)` of the local pole values. If `p ∣ m` it
follows from the invariance `d(-1 - ρ) = d(ρ)` of the reflected index; if `p ∤ m` it follows
from `ε_s(-1 - z) = -ε_{-1-s}` together with the antisymmetry `τ^an(f(-1 - z)) = -τ^an(f)`.
The result then follows from the formula `𝒯_p(1; {r}) = p^{-5} ∑_{a=0}^{p-1} w_p(r - a)` after
reindexing the sum by `a ↦ p - 1 - a`.

## Main results

* `Zeta5Irr.localPoleValue_neg_sub_self`: `w_p(-m - p) = w_p(m)`.
* `Zeta5Irr.tauDist_singleton_neg_one_sub`: `𝒯_p(1; {-1 - r}) = 𝒯_p(1; {r})`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The local pole values are symmetric under `m ↦ -m - p`: `w_p(-m - p) = w_p(m)` for a prime
`p ≥ 5`. -/
theorem localPoleValue_neg_sub_self (hp5 : 5 ≤ p) (m : ℤ) :
    localPoleValue p (-m - p) = localPoleValue p m := by
  by_cases h : (p : ℤ) ∣ m
  · obtain ⟨ρ, rfl⟩ := h
    rw [show -(p * ρ) - (p : ℤ) = p * (-1 - ρ) by ring, localPoleValue_mul_left,
      localPoleValue_mul_left, reflectIndex_neg_one_sub]
  · have h' : ¬(p : ℤ) ∣ -m - p := fun h' => h (by
      have := dvd_sub (dvd_neg.mpr h') (dvd_refl (p : ℤ))
      simpa using this)
    rw [localPoleValue_of_not_dvd h, localPoleValue_of_not_dvd h']
    congr 1
    have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hneg : ((m : ℚ_[p]) / p).valuation < 0 := by
      rw [valuation_intCast_div_prime h]; exact neg_one_lt_zero
    have hmem := (farEps_mem_tateAlgebra_and_tateNorm hneg).1
    have hs : (((-m - p : ℤ) : ℚ_[p]) / p) = -1 - (m : ℚ_[p]) / p := by
      push_cast
      field_simp
      ring
    rw [hs, ← neg_neg (farEps (-1 - _)),
      ← tateSubst_neg_one_neg_one_farEps_of_valuation_neg hneg,
      ← neg_one_smul ℚ_[p], tauAn_smul, tauAn_tateSubst_neg_one_neg_one hp5 hmem]
    ring

/-- **Reflection symmetry of `𝒯_p(1; {r})`.** For a prime `p ≥ 5` and `r ∈ ℤ`,
`𝒯_p(1; {-1 - r}) = 𝒯_p(1; {r})`. -/
@[zeta5irr "lem_tau_dist_reflect"]
theorem tauDist_singleton_neg_one_sub (hp5 : 5 ≤ p) (r : ℤ) :
    tauDist p {-1 - r} 1 = tauDist p {r} 1 := by
  rw [tauDist_singleton_one, tauDist_singleton_one, ← Finset.sum_range_reflect]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha : a < p := Finset.mem_range.mp ha
  rw [← localPoleValue_neg_sub_self hp5]
  congr 1
  push_cast [Nat.sub_sub, Nat.cast_sub (show 1 + a ≤ p by omega)]
  ring

end Zeta5Irr
