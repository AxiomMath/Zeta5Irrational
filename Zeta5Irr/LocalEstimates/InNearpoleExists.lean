/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# Every residue class meets the far poles

Let `K = 40 n` be the pole bound and `N = 3 n` the inner degree. For a modulus `p` with
`p ≤ K / 3` and any integer `σ`, some integer `r` with `N < r ≤ K` is congruent to `σ`
modulo `p`. Indeed `N + p ≤ K`, so the `p` consecutive integers `N + 1, …, N + p` all lie
in the range, and they run through every residue class modulo `p`.

## Main results

* `Zeta5Irr.exists_innerDegree_lt_le_poleBound_modEq`: for `0 < p` with `3 p ≤ K` and any
  `σ : ℤ`, there is `r : ℤ` with `N < r ≤ K` and `r ≡ σ [ZMOD p]`.

## Implementation notes

* The source takes `p` prime. Only `0 < p` is used, so the statement is proved for an
  arbitrary positive modulus; the hypothesis `p ≤ K / 3` is written `3 p ≤ K`, which is
  equivalent over the naturals. Positivity of `n` follows from `0 < p` and `3 p ≤ K`.
* The witness is explicit: `r = N + 1 + ((σ - N - 1) mod p)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5: the inner range, the entry valuations.
-/

@[expose] public section

namespace Zeta5Irr

/-- For a positive modulus `p` with `3 p ≤ K = 40 n` and any integer `σ`, some integer `r`
with `N < r ≤ K` (where `N = 3 n`) is congruent to `σ` modulo `p`. -/
@[zeta5irr "lem_in_nearpole_exists"]
theorem exists_innerDegree_lt_le_poleBound_modEq {n p : ℕ} (hp : 0 < p)
    (hpK : 3 * p ≤ poleBound n) (σ : ℤ) :
    ∃ r : ℤ, (innerDegree n : ℤ) < r ∧ r ≤ poleBound n ∧ r ≡ σ [ZMOD p] := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  set a : ℤ := (innerDegree n : ℤ) + 1
  refine ⟨a + (σ - a) % p, ?_, ?_, ?_⟩
  · have := Int.emod_nonneg (σ - a) hp'.ne'
    omega
  · have h1 := Int.emod_lt_of_pos (σ - a) hp'
    have h2 : ((3 * p : ℕ) : ℤ) ≤ (poleBound n : ℤ) := by exact_mod_cast hpK
    simp only [poleBound, innerDegree, a] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    omega
  · rw [Int.ModEq, Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.add_emod]
    simp

end Zeta5Irr
