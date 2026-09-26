/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDistSingle

/-!
# The distributed functional of the pole at the origin

Let `p` be a prime. For the single pole `R = {0}` and numerator `A = 1`, the distributed
functional is `𝒯_p(1; {0}) = -X`.

By the single-pole formula, `𝒯_p(1; {0}) = p^{-5} ∑_{a=0}^{p-1} w_p(-a)`. The term `a = 0` is
`w_p(0) = -Y_p`, and the terms `1 ≤ a ≤ p - 1` are `τ^an(ε_{-a/p})`, which sum to `C_p`. Since
`Y_p = p^5 X + C_p`, the total is `p^{-5}(-p^5 X - C_p + C_p) = -X`.

## Main results

* `Zeta5Irr.tauDist_singleton_zero_one`: `𝒯_p(1; {0}) = -X`.

## Implementation notes

The source states the result for primes `p ≥ 5`; the argument uses only that `p` is prime, and
the result is stated here for every prime `p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **`𝒯_p(1; {0}) = -X`.** The distributed functional of the single pole at the origin with
numerator `1` is `-X`. -/
@[zeta5irr "lem_tau_dist_recip"]
theorem tauDist_singleton_zero_one : tauDist p {0} 1 = -X := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℚ_[p]) ^ 5 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hsum : ∑ a ∈ Finset.Ico 1 p, localPoleValue p (0 - a) = C (Cp p) := by
    rw [Cp, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp ha
    have hnd : ¬(p : ℤ) ∣ 0 - a := by
      rw [zero_sub, Int.dvd_neg]
      exact fun h => absurd (Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp h)) (by omega)
    rw [localPoleValue_of_not_dvd hnd]
    push_cast
    rw [zero_sub, neg_div]
  rw [tauDist_singleton_one, Finset.sum_range_eq_add_Ico _ hp.pos, hsum]
  simp only [Nat.cast_zero, sub_zero, localPoleValue_zero, Yp]
  rw [neg_add, neg_add_cancel_right, smul_neg, ← smul_eq_C_mul, smul_smul,
    inv_mul_cancel₀ hp0, one_smul]

end Zeta5Irr
