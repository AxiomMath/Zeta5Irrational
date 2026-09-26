/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauFarShift

/-!
# Reflecting the far-pole series `ε_s`

For `s ∈ ℚ_p` with `v_p(s) < 0`, the substitution `z ↦ -1 - z` carries the far-pole series
`ε_s = -∑_{k ≥ 0} s^{-k-1} z^k`, the expansion of `1 / (z - s)`, to the expansion of
`1 / (-1 - z - s) = -1 / (z - (-1 - s))`:
`ε_s(-1 - z) = -ε_{-1-s}`.

## Main results

* `Zeta5Irr.tateSubst_neg_one_neg_one_farEps`: `ε_s(-1 - z) = -ε_{-1-s}` for `|s|_p > 1`.
* `Zeta5Irr.tateSubst_neg_one_neg_one_farEps_of_valuation_neg`: the statement of the source,
  for `v_p(s) < 0`.

## Implementation notes

* The source argues by uniqueness of inverses: substitution is a ring homomorphism, so
  `(z - (-1 - s)) (-ε_s(-1 - z)) = 1 = (z - (-1 - s)) ε_{-1-s}`. Here the substitution
  `tateSubst` is defined coefficientwise, and the statement is the case `u = c = -1` of
  `Zeta5Irr.tateSubst_farEps`, proved by comparing coefficients.
* The main statement is proved under `1 < |s|_p`, which is equivalent to `v_p(s) < 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- For `s ∈ ℚ_p` with `|s|_p > 1`, the substitution `z ↦ -1 - z` carries `ε_s` to
`-ε_{-1-s}`. -/
theorem tateSubst_neg_one_neg_one_farEps {s : ℚ_[p]} (hs : 1 < ‖s‖) :
    tateSubst (-1) (-1) (farEps s) = -farEps (-1 - s) := by
  rw [tateSubst_farEps (by simp) (by simp) hs, inv_neg, inv_one, neg_one_smul]
  congr 2
  ring

/-- **Reflecting `ε_s`.** For `s ∈ ℚ_p` with `v_p(s) < 0`, `ε_s(-1 - z) = -ε_{-1-s}`. -/
@[zeta5irr "lem_tau_far_reflect"]
theorem tateSubst_neg_one_neg_one_farEps_of_valuation_neg {s : ℚ_[p]} (hs : s.valuation < 0) :
    tateSubst (-1) (-1) (farEps s) = -farEps (-1 - s) :=
  tateSubst_neg_one_neg_one_farEps (one_lt_norm_of_valuation_neg hs)

end Zeta5Irr
