/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.QRK
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Counting the points of `R_K` in a small `p`-adic ball

Let `p` be a prime, `i ≥ 1` and `x ∈ ℤ_p`. The points `s ∈ R_K` with `v_p(x - s) ≥ i` are
pairwise congruent modulo `p^i`, so they lie in a single residue class modulo `p^i` inside the
interval `[-K, K]` of length `2K`. Hence there are at most `⌊2K / p^i⌋ + 1` of them.

## Main results

* `Zeta5Irr.card_le_div_add_one_of_dvd_sub`: a finite set of integers inside an interval
  `[a, a + n]` whose elements are pairwise congruent modulo `d > 0` has at most `⌊n / d⌋ + 1`
  elements.
* `Zeta5Irr.card_filter_puncturedIcc_pow_dvd_sub_le`: `#{s ∈ R_K : v_p(x - s) ≥ i} ≤
  ⌊2K / p^i⌋ + 1`.

## Implementation notes

* The condition `v_p(x - s) ≥ i` for `x ∈ ℤ_p` is stated as `(p : ℤ_[p]) ^ i ∣ x - s`,
  which is its meaning in `ℤ_p` (with `v_p(0) = +∞`).
* The floor `⌊2K / p^i⌋` is written as the natural-number quotient `2 * K / p ^ i`.
* The source assumes `K ≥ 1` and `i ≥ 1`; the bound holds for all `K i : ℕ`, so these
  hypotheses are dropped.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6: small primes.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- A finite set of integers inside `[a, a + n]` whose elements are pairwise congruent modulo
`d > 0` has at most `⌊n / d⌋ + 1` elements. -/
theorem card_le_div_add_one_of_dvd_sub {S : Finset ℤ} {a : ℤ} {n d : ℕ} (hd : 0 < d)
    (hS : S ⊆ Icc a (a + n)) (hdvd : ∀ s ∈ S, ∀ t ∈ S, (d : ℤ) ∣ s - t) :
    #S ≤ n / d + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set m := S.min' hne with hm
  have hmS : m ∈ S := S.min'_mem hne
  have hma : a ≤ m := (mem_Icc.1 (hS hmS)).1
  have key : ∀ s ∈ S, s - m = d * ((s - m) / d) := fun s hs =>
    (Int.mul_ediv_cancel' (hdvd s hs m hmS)).symm
  calc #S ≤ #(range (n / d + 1)) := by
        refine card_le_card_of_injOn (fun s => ((s - m) / d).toNat) ?_ ?_
        · intro s hs
          have hs' := mem_Icc.1 (hS hs)
          have hms : m ≤ s := S.min'_le s hs
          simp only [coe_range, Set.mem_Iio]
          have h1 : (s - m) / d ≤ (n : ℤ) / d :=
            Int.ediv_le_ediv (by exact_mod_cast hd) (by omega)
          have h2 : 0 ≤ (s - m) / d := Int.ediv_nonneg (by omega) (by positivity)
          have h3 : ((n : ℤ) / d) = ((n / d : ℕ) : ℤ) := by push_cast; rfl
          omega
        · intro s hs t ht hst
          have hs0 : 0 ≤ (s - m) / d :=
            Int.ediv_nonneg (by linarith [S.min'_le s hs]) (by positivity)
          have ht0 : 0 ≤ (t - m) / d :=
            Int.ediv_nonneg (by linarith [S.min'_le t ht]) (by positivity)
          have heq : (s - m) / d = (t - m) / d := by
            simp only at hst; omega
          have h1 := key s hs
          have h2 := key t ht
          rw [heq] at h1
          linarith
    _ = n / d + 1 := card_range _

open scoped Classical in
/-- **Small primes, root count.** For a prime `p`, `x ∈ ℤ_p` and `K, i ∈ ℕ`, the number of
`s ∈ R_K` with `v_p(x - s) ≥ i` is at most `⌊2K / p^i⌋ + 1`. -/
@[zeta5irr "lem_small_rootcount"]
theorem card_filter_puncturedIcc_pow_dvd_sub_le (p : ℕ) [Fact p.Prime] (K i : ℕ) (x : ℤ_[p]) :
    #{s ∈ puncturedIcc K | (p : ℤ_[p]) ^ i ∣ x - ((s : ℤ) : ℤ_[p])} ≤
      2 * K / p ^ i + 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine card_le_div_add_one_of_dvd_sub (a := -K) (pow_pos hp i) ?_ ?_
  · intro s hs
    have := (mem_puncturedIcc.1 (mem_filter.1 hs).1).2
    rw [mem_Icc]; push_cast; omega
  · intro s hs t ht
    have h : (p : ℤ_[p]) ^ i ∣ ((s - t : ℤ) : ℤ_[p]) := by
      have := dvd_sub (mem_filter.1 ht).2 (mem_filter.1 hs).2
      push_cast
      convert this using 1
      ring
    push_cast
    exact (PadicInt.pow_p_dvd_int_iff i (s - t)).1 h

end Zeta5Irr
