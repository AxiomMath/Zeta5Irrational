/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InOrd
public import Mathlib.Data.Int.Star

/-!
# The degree bound at the zero class

Let `M ≥ 40`, `K = 40 n ≥ 200 M²` and let `p` be a prime with `K / M < p ≤ K / 3`. For classes
`0 ≤ a, c ≤ m°` and indices `0 ≤ i < L_a`, `0 ≤ j < L_c`, the vanishing orders at the zero class
satisfy
`5 + 2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 12 m_N ≤ p + 1`.

The proof bounds each `θ_{a,i}(0)` by `L₀ = 4 M + 10`, bounds `12 m_N < 9 M / 10` using
`K / p < M`, and compares with `p > K / M ≥ 200 M`.

## Main results

* `Zeta5Irr.classVanishingOrder_zero_le`: `θ_{a,i}(0) ≤ L₀` whenever `i < L_a`.
* `Zeta5Irr.five_add_classVanishingOrder_zero_add_mA_le`: the degree bound
  `5 + 2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 12 m_N ≤ p + 1`.

## Implementation notes

* The source assumes `p` prime, `p ≤ K / 3` and `a, c ≤ m°`; none of these is used in the proof,
  so the main result is stated without them. The hypothesis `K ∈ 40 ℤ_{>0}` is encoded by
  writing `K = poleBound n = 40 n`; positivity of `n` follows from `K ≥ 200 M²` and `M ≥ 40`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

/-- If `i ≤ L_a`, then the vanishing order at the zero class is at most `L₀`:
`θ_{a,i}(0) ≤ L₀ = 4 M + 10`. -/
theorem classVanishingOrder_zero_le {n p M a i : ℕ} (hi : (i : ℤ) ≤ classDimAt n p M a) :
    classVanishingOrder n p M a i 0 ≤ zeroClassDim M := by
  simpa using classVanishingOrder_le hi 0

/-- **The degree bound at the zero class.** For `M ≥ 40`, `K = 40 n ≥ 200 M²`, `K / M < p`,
`i < L_a` and `j < L_c`, we have `5 + 2 θ_{a,i}(0) + 2 θ_{c,j}(0) + 12 m_N ≤ p + 1`. -/
@[zeta5irr "lem_in_deg_zero"]
theorem five_add_classVanishingOrder_zero_add_mA_le {n p M a c i j : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ poleBound n) (hp : (poleBound n : ℚ) / M < p)
    (hi : (i : ℤ) < classDimAt n p M a) (hj : (j : ℤ) < classDimAt n p M c) :
    5 + 2 * classVanishingOrder n p M a i 0 + 2 * classVanishingOrder n p M c j 0 +
      12 * (mA p (innerDegree n) : ℤ) ≤ p + 1 := by
  have hθa := classVanishingOrder_zero_le hi.le
  have hθc := classVanishingOrder_zero_le hj.le
  obtain ⟨hpM, h200⟩ := lt_mul_and_lt_of_div_lt_of_sq_le (by omega) hK hp
  -- `m_N = ⌊N / p⌋` satisfies `40 m_N < 3 M`.
  have hq : 40 * (3 * n / p) < 3 * M := forty_mul_mA_innerDegree_lt hpM
  simp only [poleBound] at hK hpM
  have hq' : 40 * ((3 * n / p : ℕ) : ℤ) < 3 * M := by exact_mod_cast hq
  have h200' : 200 * (M : ℤ) < p := by exact_mod_cast h200
  simp only [mA, innerDegree, cast_zeroClassDim] at hθa hθc ⊢
  omega

end Zeta5Irr
