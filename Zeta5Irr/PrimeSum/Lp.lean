/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.ScalingFactor
public import Zeta5Irr.LocalEstimates.GammaIn
public import Zeta5Irr.LocalEstimates.GammaOut
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The local exponents `L_p(K, M)`

For an integer `M ≥ 40`, an integer `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`, and a prime `p`, the
local exponent is
```
L_p(K, M) = -6 h ⌊log_p (5K)⌋ - h v_p(24)     if p M ≤ K,
L_p(K, M) = v_p(S_K) + γ_p^in                  if p M > K and 3 p ≤ K,
L_p(K, M) = v_p(S_K) + γ_p^out                 if 3 p > K and p ≤ K,
L_p(K, M) = v_p(S_K)                           if p > K,
```
where `K = 40 n`, `N = 3 n`, `h = 37 n`, `S_K` is the scaling factor, and `γ_p^in`, `γ_p^out`
are the inner and outer exponents. These are the exponents of the normalizing factor
`m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}`, chosen so that `m_{K,M} F_K` is integral.

## Main definitions

* `Zeta5Irr.localExponent`: the local exponent `L_p(K, M)`.

## Main results

* `Zeta5Irr.localExponent_of_mul_le`: the value `-6 h ⌊log_p (5K)⌋ - h v_p(24)` when
  `p M ≤ K`, with the floor of the real logarithm.
* `Zeta5Irr.localExponent_of_inner`, `Zeta5Irr.localExponent_of_outer`,
  `Zeta5Irr.localExponent_of_lt`: the values in the other three cases; the last two assume
  `M ≥ 3` and `M ≥ 1` respectively, which make the condition `p M > K` automatic.

## Implementation notes

* Since `K = 40 n`, `S_K`, `γ_p^in` and `γ_p^out` are all indexed by `n`, the exponent is
  indexed by `n`, `M` and `p`, and `K` is `Zeta5Irr.poleBound n`.
* The exponent is rational-valued: `γ_p^in` is a sum of weights some of which are
  half-integers, and its integrality is a separate result. The source's hypotheses
  (`M ≥ 40`, `K ≥ 200 M²`, `p` prime) are not needed to write the four cases down, so the
  definition is total and those hypotheses appear only in lemmas about it.
* `⌊log_p (5K)⌋` is `Nat.log p (5K)`, and `v_p` of the integer `24` is `padicValNat p 24`;
  `Zeta5Irr.localExponent_of_mul_le` restates the first case with `⌊Real.logb p (5K)⌋`.
* The fourth case is the source's convention "for `p > K`, put `γ_p^out = 0`".

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1 (The normalizing factor and integrality).
-/

@[expose] public section

namespace Zeta5Irr

/-- The local exponent `L_p(K, M)`, with `K = 40 n`, `N = 3 n` and `h = 37 n`: it is
`-6 h ⌊log_p (5K)⌋ - h v_p(24)` if `p M ≤ K`, `v_p(S_K) + γ_p^in` if `p M > K` and `3 p ≤ K`,
`v_p(S_K) + γ_p^out` if `3 p > K` and `p ≤ K`, and `v_p(S_K)` if `p > K`. -/
@[zeta5irr "def_Lp"]
def localExponent (n M p : ℕ) : ℚ :=
  if p * M ≤ poleBound n then
    -6 * matrixOrder n * Nat.log p (5 * poleBound n) - matrixOrder n * padicValNat p 24
  else if 3 * p ≤ poleBound n then
    padicValRat p (scalingFactor n) + innerExponent n p M
  else if p ≤ poleBound n then
    padicValRat p (scalingFactor n) + outerExponent p (innerDegree n) (poleBound n)
  else
    padicValRat p (scalingFactor n)

variable {n M p : ℕ}

/-- If `p M ≤ K`, then `L_p(K, M) = -6 h ⌊log_p (5K)⌋ - h v_p(24)`, with `⌊log_p (5K)⌋`
computed as `Nat.log p (5K)`. -/
theorem localExponent_of_mul_le_natLog (h : p * M ≤ poleBound n) :
    localExponent n M p =
      -6 * matrixOrder n * Nat.log p (5 * poleBound n) - matrixOrder n * padicValNat p 24 :=
  ite_eq_left h

/-- If `p M ≤ K`, then `L_p(K, M) = -6 h ⌊log_p (5K)⌋ - h v_p(24)`, with the floor of the
real logarithm to base `p`. -/
theorem localExponent_of_mul_le (h : p * M ≤ poleBound n) :
    localExponent n M p =
      -6 * matrixOrder n * ⌊Real.logb p (5 * poleBound n : ℕ)⌋ -
        matrixOrder n * padicValNat p 24 := by
  rw [localExponent_of_mul_le_natLog h, Real.floor_logb_natCast (Nat.cast_nonneg _),
    Int.log_natCast]
  push_cast
  rfl

/-- If `p M > K` and `3 p ≤ K`, then `L_p(K, M) = v_p(S_K) + γ_p^in`. -/
theorem localExponent_of_inner (h₁ : poleBound n < p * M) (h₂ : 3 * p ≤ poleBound n) :
    localExponent n M p = padicValRat p (scalingFactor n) + innerExponent n p M := by
  simp only [localExponent, Nat.not_le.2 h₁, h₂, ↓reduceIte]

/-- If `p M > K`, `3 p > K` and `p ≤ K`, then `L_p(K, M) = v_p(S_K) + γ_p^out`. The first
condition follows from the second when `M ≥ 3`; see `Zeta5Irr.localExponent_of_outer`. -/
theorem localExponent_of_outer' (h₀ : poleBound n < p * M) (h₁ : poleBound n < 3 * p)
    (h₂ : p ≤ poleBound n) :
    localExponent n M p =
      padicValRat p (scalingFactor n) + outerExponent p (innerDegree n) (poleBound n) := by
  simp only [localExponent, Nat.not_le.2 h₀, Nat.not_le.2 h₁, h₂, ↓reduceIte]

/-- If `M ≥ 3`, `3 p > K` and `p ≤ K`, then `L_p(K, M) = v_p(S_K) + γ_p^out`. -/
theorem localExponent_of_outer (hM : 3 ≤ M) (h₁ : poleBound n < 3 * p)
    (h₂ : p ≤ poleBound n) :
    localExponent n M p =
      padicValRat p (scalingFactor n) + outerExponent p (innerDegree n) (poleBound n) :=
  localExponent_of_outer' (h₁.trans_le (Nat.mul_comm 3 p ▸ Nat.mul_le_mul_left p hM)) h₁ h₂

/-- If `p M > K` and `p > K`, then `L_p(K, M) = v_p(S_K)`. The first condition follows from
the second when `M ≥ 1`; see `Zeta5Irr.localExponent_of_lt`. -/
theorem localExponent_of_lt' (h₀ : poleBound n < p * M) (h : poleBound n < p) :
    localExponent n M p = padicValRat p (scalingFactor n) := by
  simp only [localExponent, Nat.not_le.2 h₀, Nat.not_le.2 h, ↓reduceIte,
    show ¬ 3 * p ≤ poleBound n by omega]

/-- If `M ≥ 1` and `p > K`, then `L_p(K, M) = v_p(S_K)`. -/
theorem localExponent_of_lt (hM : 1 ≤ M) (h : poleBound n < p) :
    localExponent n M p = padicValRat p (scalingFactor n) :=
  localExponent_of_lt' (h.trans_le (Nat.le_mul_of_pos_right p hM)) h

end Zeta5Irr
