/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InEps

/-!
# The extras go to the classes of largest `ℓ_K`

For an odd prime `p`, an integer `M ≥ 40` and `1 ≤ a, c ≤ m°` with `ε_a = 1` and `ε_c = 0`,
we have `ℓ_K(a) ≥ ℓ_K(c)`: the classes receiving an extra dimension have values of `ℓ_K` at
least as large as those that do not.

The proof goes through the rank: `ε_a = 1` and `ε_c = 0` give `rk(a) < E ≤ rk(c)`. If we had
`ℓ_K(c) > ℓ_K(a)`, every index counted by `rk(c)` would satisfy `ℓ_K(c') ≥ ℓ_K(c) > ℓ_K(a)`
and so be counted by `rk(a)`, whence `rk(c) ≤ rk(a)`, a contradiction.

## Main results

* `Zeta5Irr.ellA_le_of_inRank_lt`: if `rk(a) < rk(c)` then `ℓ_K(c) ≤ ℓ_K(a)`.
* `Zeta5Irr.ellA_le_of_extraIndicator`: if `ε_a = 1` and `ε_c = 0` then `ℓ_K(c) ≤ ℓ_K(a)`.

## Implementation notes

* The hypotheses that `p` is an odd prime, `M ≥ 40` and `1 ≤ a, c ≤ m°` are not needed: the
  inclusion of the set counted by `rk(c)` in the set counted by `rk(a)` holds for all indices.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The rank is antitone in `ℓ_K`, in the sense that `rk(a) < rk(c)` forces
`ℓ_K(c) ≤ ℓ_K(a)`. -/
theorem ellA_le_of_inRank_lt {p K a c : ℕ} (h : inRank p K a < inRank p K c) :
    ellA p K c ≤ ellA p K a := by
  refine le_of_not_gt fun hlt => ?_
  refine h.not_ge (card_le_card fun c' hc' => ?_)
  simp only [mem_filter] at hc' ⊢
  refine ⟨hc'.1, Or.inl ?_⟩
  rcases hc'.2 with h' | ⟨h', -⟩
  · exact hlt.trans h'
  · exact h' ▸ hlt

/-- If `ε_a = 1` and `ε_c = 0`, then `ℓ_K(c) ≤ ℓ_K(a)`, where `K = 40 n`. -/
@[zeta5irr "lem_in_eps_order"]
theorem ellA_le_of_extraIndicator {n p M a c : ℕ} (ha : extraIndicator n p M a = 1)
    (hc : extraIndicator n p M c = 0) :
    ellA p (poleBound n) c ≤ ellA p (poleBound n) a := by
  rw [extraIndicator_eq_one_iff] at ha
  rw [extraIndicator_eq_zero_iff] at hc
  exact ellA_le_of_inRank_lt (by exact_mod_cast ha.trans_le hc)

end Zeta5Irr
