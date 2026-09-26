/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InMstar
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# The valuation of a difference of squares of nodes

Let `p` be a prime, let `1 ≤ a ≤ m° = (p - 1) / 2`, and let `j ≠ j'` be integers with
`1 ≤ j, j' ≤ K`, `2 K < p ^ 2`, and `j ≡ ± a`, `j' ≡ ± a` modulo `p`. Then
`v_p (j ^ 2 - j' ^ 2) = 1`.

Write `j ^ 2 - j' ^ 2 = (j - j') (j + j')`. Both factors are nonzero, and since `0 < 2 a < p`,
`p` does not divide `2 j'`. Hence exactly one of the two factors is divisible by `p`: the first
if `j ≡ j'`, the second if `j ≡ -j'`. That factor has absolute value less than `p ^ 2`, so its
valuation is exactly `1`, while the other factor has valuation `0`.

## Main results

* `Zeta5Irr.padicValInt_sq_sub_sq_eq_one`: `v_p (j ^ 2 - j' ^ 2) = 1` under the hypotheses above.
* `Zeta5Irr.padicValInt_eq_one_of_dvd_of_natAbs_lt`: a nonzero multiple of `p` of absolute value
  less than `p ^ 2` has `p`-adic valuation `1`.

## Implementation notes

* The source assumes in addition `p ≥ 7` and `p ≤ K < 3 p`. These are not used: primality of
  `p` and `2 K < p ^ 2` suffice (the hypothesis `1 ≤ a ≤ m°` already excludes `p = 2`).
* The congruences `j ≡ ± a (mod p)` are stated with `Int.ModEq`, for integers `j`, `j'`, `a`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.10 (The outer range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

/-- A nonzero integer divisible by the prime `p` and of absolute value less than `p ^ 2` has
`p`-adic valuation exactly `1`. -/
theorem padicValInt_eq_one_of_dvd_of_natAbs_lt {p : ℕ} [hp : Fact p.Prime] {x : ℤ}
    (hx : x ≠ 0) (hdvd : (p : ℤ) ∣ x) (hlt : x.natAbs < p ^ 2) : padicValInt p x = 1 := by
  have h1 : 1 ≤ padicValInt p x :=
    ((padicValInt_dvd_iff (p := p) 1 x).1 (by simpa using hdvd)).resolve_left hx
  have h2 : padicValInt p x < 2 := by
    by_contra h
    have h' : ((p : ℤ) ^ 2) ∣ x := (padicValInt_dvd_iff 2 x).2 (Or.inr (by omega))
    have := Nat.le_of_dvd (Int.natAbs_pos.2 hx) (by
      simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.2 h')
    omega
  omega

/-- **Valuation of a difference of squares of nodes.** Let `p` be a prime, `1 ≤ a ≤ m°`, and let
`j ≠ j'` be integers in `[1, K]` with `2 K < p ^ 2`, each congruent to `± a` modulo `p`. Then
`v_p (j ^ 2 - j' ^ 2) = 1`. -/
@[zeta5irr "lem_out_node_diff"]
theorem padicValInt_sq_sub_sq_eq_one {p : ℕ} [hp : Fact p.Prime] {K : ℕ} (hK : 2 * K < p ^ 2)
    {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ mStar p) {j j' : ℤ} (hjj' : j ≠ j')
    (hj : 1 ≤ j) (hjK : j ≤ K) (hj' : 1 ≤ j') (hj'K : j' ≤ K)
    (hja : j ≡ a [ZMOD p] ∨ j ≡ -a [ZMOD p]) (hj'a : j' ≡ a [ZMOD p] ∨ j' ≡ -a [ZMOD p]) :
    padicValInt p (j ^ 2 - j' ^ 2) = 1 := by
  have h2a : 2 * a < p := by
    have := hp.out.two_le
    rw [mStar_def] at ha'
    omega
  -- Exactly one of `j - j'` and `j + j'` is divisible by `p`, since `p ∤ 2 a`.
  have hcases : ((p : ℤ) ∣ j - j' ∧ ¬ (p : ℤ) ∣ j + j') ∨
      (¬ (p : ℤ) ∣ j - j' ∧ (p : ℤ) ∣ j + j') := by
    have h0 : ((a : ZMod p) + a) ≠ 0 := by
      have : ((2 * a : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      push_cast at this
      rwa [two_mul] at this
    have h0' : -((a : ZMod p) + a) ≠ 0 := neg_ne_zero.2 h0
    simp only [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hja hj'a ⊢
    push_cast at hja hj'a ⊢
    rcases hja with h | h <;> rcases hj'a with h' | h' <;> rw [h, h'] <;>
      [left; right; right; left] <;> refine ⟨?_, ?_⟩ <;> ring_nf at h0 h0' ⊢ <;> simp_all
  have hd0 : j - j' ≠ 0 := sub_ne_zero.2 hjj'
  have hs0 : j + j' ≠ 0 := by omega
  rw [sq_sub_sq, mul_comm, padicValInt.mul hd0 hs0]
  rcases hcases with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · rw [padicValInt_eq_one_of_dvd_of_natAbs_lt hd0 hd (by omega), padicValInt.eq_zero_of_not_dvd hs]
  · rw [padicValInt_eq_one_of_dvd_of_natAbs_lt hs0 hs (by omega), padicValInt.eq_zero_of_not_dvd hd]

end Zeta5Irr
