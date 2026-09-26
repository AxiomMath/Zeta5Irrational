/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InEllFormula
public import Zeta5Irr.LocalEstimates.OutDelta
public import Zeta5Irr.LocalEstimates.OutMN

/-!
# `ℓ_N(a) = δ_a` in the outer range

Let `p` be an odd prime with `2N < p` and `1 ≤ a ≤ m° = (p - 1) / 2`. Then `ℓ_N(a) = δ_a`.

Indeed `m_N = 0`, so `v_N = N`, and the formula for `ℓ_A` gives
`ℓ_N(a) = 𝟙[a ≤ N] + 𝟙[p - a ≤ N]`. The second indicator vanishes, because
`p - a ≥ (p + 1) / 2 > p / 2 > N`. Hence `ℓ_N(a) = 𝟙[a ≤ N] = δ_a`.

## Main results

* `Zeta5Irr.ellA_eq_outerDelta`: if `2N < p` and `1 ≤ a ≤ m°` then `ℓ_N(a) = δ_a`.

## Implementation notes

* The source assumes `p` is an odd prime. Neither primality nor oddness is used, so the lemma
  is stated for an arbitrary natural number `p`; the threshold `N` is an arbitrary natural
  number, matching `Zeta5Irr.outerDelta`, which takes it as an integer argument.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.8 (The outer range: the separating basis).
-/

@[expose] public section

namespace Zeta5Irr

/-- **`ℓ_N(a) = δ_a` in the outer range.** If `2N < p` and `1 ≤ a ≤ m°`, then
`ℓ_N(a) = δ_a`. -/
@[zeta5irr "lem_out_ellN"]
theorem ellA_eq_outerDelta {p N a : ℕ} (h : 2 * N < p) (ha : 1 ≤ a) (ham : a ≤ mStar p) :
    ellA p N a = outerDelta N a := by
  have h2a : 2 * a < p := by rw [mStar_def] at ham; omega
  have hv : vA p N = N := by
    have := mul_mA_add_vA p N
    rw [mA_eq_zero_of_two_mul_lt h] at this
    omega
  rw [ellA_eq_two_mul_mA_add ha ham, mA_eq_zero_of_two_mul_lt h, hv, outerDelta]
  split_ifs <;> omega

end Zeta5Irr
