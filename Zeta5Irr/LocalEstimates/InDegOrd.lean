/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InOrd
public import Zeta5Irr.LocalEstimates.InTUpper

/-!
# The degree bound for the entry valuations of the inner range

Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, and let `p` be a prime with `K / M < p ≤ K / 3`. For
indices `0 ≤ a, c ≤ m°`, integers `0 ≤ i < L_a`, `0 ≤ j < L_c` and `1 ≤ s ≤ m°`, the class
vanishing orders satisfy
`θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) ≤ p + 1`.

Each order is at most `L_s = T - b_s + ε_s` with `b_s = 3 ℓ_N(s)` and `ε_s ≤ 1`, so the left
side is at most `2 T + 2`. The upper bound `T < 2 H K / p < 2 H M = 23 M / 10` and the lower
bound `p > K / M ≥ 200 M` then give `2 T + 2 < p + 1`.

## Main results

* `Zeta5Irr.classVanishingOrder_add_add_le`: the degree bound
  `θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) ≤ p + 1`.

## Implementation notes

* Of the hypotheses of the source, the upper bound `p ≤ K / 3` and the ranges `a, c ≤ m°`,
  `s ≤ m°` are not needed, and are omitted; only `1 ≤ s` is used, so that `L_s` is the class
  dimension `T - b_s + ε_s` rather than the zero-class dimension.
* The integer `K` is `poleBound n = 40 n` and `N` is `innerDegree n = 3 n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

/-- **Degree bound for the entry valuations.** Let `M ≥ 40`, let `K = 40 n ≥ 200 M²`, and let `p`
be a prime with `K / M < p`. If `i < L_a`, `j < L_c` and `1 ≤ s`, then
`θ_{a,i}(s) + θ_{c,j}(s) + 6 ℓ_N(s) ≤ p + 1`. The source also assumes `p ≤ K / 3` and
`a, c, s ≤ m°`, which are not needed. -/
@[zeta5irr "lem_in_deg_ord"]
theorem classVanishingOrder_add_add_le {n M p a c i j s : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : p.Prime) (hpK : (poleBound n : ℝ) / M < p)
    (hi : (i : ℤ) < classDimAt n p M a) (hj : (j : ℤ) < classDimAt n p M c) (hs : 1 ≤ s) :
    classVanishingOrder n p M a i s + classVanishingOrder n p M c j s +
      6 * ellA p (innerDegree n) s ≤ p + 1 := by
  obtain ⟨hlt, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le (by omega) hK hpK
  have hp2 : 2 < p := by omega
  have hT := commonClassDim_mul_lt_of_odd (hp.odd_of_ne_two hp2.ne') hp.one_lt hlt
  -- each order is at most `L_s ≤ T - b_s + 1`
  have hLs : classDimAt n p M s ≤
      commonClassDim n p M - 3 * ellA p (innerDegree n) s + 1 := by
    rw [classDimAt_of_ne_zero _ _ _ (by omega : s ≠ 0)]
    simpa using innerClassDim_le n p M s
  have h1 := classVanishingOrder_le hi.le s
  have h2 := classVanishingOrder_le hj.le s
  -- `2 T + 1 ≤ p`
  have hTp : 2 * commonClassDim n p M + 1 ≤ p := by
    set T := commonClassDim n p M
    simp only [poleBound] at hK hlt
    have hK' : (200 * M ^ 2 : ℤ) ≤ 40 * n := by exact_mod_cast hK
    have hlt' : (40 * n : ℤ) < p * M := by exact_mod_cast hlt
    have hM'' : (40 : ℤ) ≤ M := by exact_mod_cast hM
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    -- `p > 200 M`
    have hp200 : (200 * M : ℤ) < p := by nlinarith
    -- `40 T < 92 M`
    have h40 : 40 * T < 92 * M := by
      by_contra! h
      nlinarith
    omega
  omega

end Zeta5Irr
