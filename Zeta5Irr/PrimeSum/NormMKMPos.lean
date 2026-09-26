/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.MKM
public import Zeta5Irr.LocalEstimates.InGinInteger

/-!
# The normalizing factor `m_{K,M}` is a positive rational number

For every integer `M ≥ 40` and every `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, the normalizing factor
`m_{K,M} = ∏_{p ≤ 2h} p ^ (-L_p(K, M))` is a positive rational number.

Each local exponent `L_p(K, M)` is an integer: in its first case it is
`-6 h ⌊log_p (5K)⌋ - h v_p(24)`, an integer combination of integers; in the other cases it is
`v_p(S_K)` plus `γ_p^in`, `γ_p^out` or `0`, where `v_p(S_K)` is an integer, `γ_p^in` is an
integer by `Zeta5Irr.exists_innerExponent_eq_intCast`, and `γ_p^out` is an integer by
definition. Hence each factor `p ^ (-L_p(K, M))` is a positive rational number, and so is
their finite product.

## Main results

* `Zeta5Irr.exists_localExponent_eq_intCast`: the local exponent `L_p(K, M)` is an integer.
* `Zeta5Irr.exists_normalizingFactor_eq_ratCast`: `m_{K,M}` is a positive rational number.

## Implementation notes

* The source's hypotheses `M ≥ 40`, `K ∈ 40 ℤ_{>0}` and `K ≥ 200 M²` are not needed: the
  local exponent is an integer for all `n`, `M` and `p`, so the results are stated without
  them.
* The `p`-adic valuation `v_p(S_K)` of the rational number `S_K` is integer-valued by
  construction (`padicValRat`), and `γ_p^out` is defined as an integer, so only `γ_p^in`
  needs an argument.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1 (The normalizing factor and integrality).
-/

@[expose] public section

namespace Zeta5Irr

/-- The local exponent `L_p(K, M)` is an integer. -/
theorem exists_localExponent_eq_intCast (n M p : ℕ) : ∃ z : ℤ, localExponent n M p = z := by
  obtain ⟨g, hg⟩ := exists_innerExponent_eq_intCast n p M
  unfold localExponent
  split_ifs
  · exact ⟨-6 * matrixOrder n * Nat.log p (5 * poleBound n) - matrixOrder n * padicValNat p 24,
      by simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast]⟩
  · exact ⟨padicValRat p (scalingFactor n) + g, by rw [hg]; push_cast; rfl⟩
  · exact ⟨padicValRat p (scalingFactor n) + outerExponent p (innerDegree n) (poleBound n),
      by push_cast; rfl⟩
  · exact ⟨padicValRat p (scalingFactor n), rfl⟩

/-- The normalizing factor `m_{K,M}` is a positive rational number. -/
@[zeta5irr "lem_norm_mKM_pos"]
theorem exists_normalizingFactor_eq_ratCast (n M : ℕ) :
    ∃ q : ℚ, 0 < q ∧ normalizingFactor n M = q := by
  choose e he using exists_localExponent_eq_intCast n M
  refine ⟨_, Finset.prod_pos fun p hp => zpow_pos ?_ _,
    normalizingFactor_eq_ratCast fun p _ => he p⟩
  exact Nat.cast_pos.2 (Nat.prime_of_mem_primesBelow hp).pos

end Zeta5Irr
