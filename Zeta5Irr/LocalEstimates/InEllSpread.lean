/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InEllFormula

/-!
# The values `ℓ_A(a)`, `1 ≤ a ≤ m°`, differ by at most one

Let `p` be an odd prime, `A ≥ 0` and `1 ≤ a, c ≤ m° = (p - 1) / 2`. Then
`|ℓ_A(a) - ℓ_A(c)| ≤ 1`.

By the closed formula `ℓ_A(a) = 2 m_A + 𝟙[a ≤ v_A] + 𝟙[p - a ≤ v_A]`, it suffices to see that
the correction term `𝟙[a ≤ v_A] + 𝟙[p - a ≤ v_A] ∈ {0, 1, 2}` never takes both values `0`
and `2`. If it equals `2` at some `a`, then `v_A ≥ p - a ≥ p - m°`, and every `c ≤ m°` satisfies
`c < p - m° ≤ v_A`, so the correction term is at least `1` at every `c`.

## Main results

* `Zeta5Irr.abs_ellA_sub_ellA_le_one`: `|ℓ_A(a) - ℓ_A(c)| ≤ 1` for `1 ≤ a, c ≤ m°`.

## Implementation notes

* The source assumes `p` is an odd prime. As for the closed formula, neither primality nor
  oddness is used, so the statement is made for an arbitrary natural number `p`. The absolute
  value is taken in `ℤ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.2: square classes modulo a prime.
-/

@[expose] public section

namespace Zeta5Irr

/-- **Spread of `ℓ_A` on `[1, m°]`.** For `1 ≤ a, c ≤ m° = (p - 1) / 2`,
`|ℓ_A(a) - ℓ_A(c)| ≤ 1`. -/
@[zeta5irr "lem_in_ell_spread"]
theorem abs_ellA_sub_ellA_le_one {p a c : ℕ} (ha : 1 ≤ a) (ham : a ≤ mStar p) (hc : 1 ≤ c)
    (hcm : c ≤ mStar p) (A : ℕ) :
    |((ellA p A a : ℕ) : ℤ) - ellA p A c| ≤ 1 := by
  rw [ellA_eq_two_mul_mA_add ha ham, ellA_eq_two_mul_mA_add hc hcm, abs_le]
  rw [mStar_def] at ham hcm
  constructor <;> split_ifs <;> push_cast <;> omega

end Zeta5Irr
