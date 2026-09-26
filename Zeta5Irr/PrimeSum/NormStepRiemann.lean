/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Riemann sums of step functions sampled at `a / p`

Let `0 = z₀ < z₁ < ⋯ < z_r = 1/2` and let `G` be a function which is constant, equal to `c_k`,
on each open interval `(z_{k-1}, z_k)`, and bounded by `C` on `(0, 1/2)`. Then the Riemann sum
`∑_{a=1}^{(p-1)/2} G(a/p)` differs from `p ∫_0^{1/2} G` by at most `2 r C`.

On one interval `(u, v)` the integers `a` with `u < a/p < v` are those of the integer interval
`(⌊p u⌋, ⌈p v⌉)`, whose cardinality differs from `p (v - u)` by less than `1`; this costs at
most `|c_k| ≤ C`. Each of the `r - 1` interior break points `z_k` may be a sample point `a/p`,
at a further cost of at most `C` each.

## Main results

* `Zeta5Irr.abs_sum_indicator_Ioo_sub_integral_le`: the estimate on a single interval where
  `G` is constant.
* `Zeta5Irr.abs_sum_indicator_sub_integral_le_of_step`: the estimate for a step function on an
  arbitrary partition `z₀ < ⋯ < z_r`, with error `2 r C`; the step function is also
  interval integrable.
* `Zeta5Irr.abs_sum_step_sub_integral_le`: the blueprint's statement, for the partition of
  `[0, 1/2]` and the sum over `1 ≤ a ≤ (p - 1)/2`.

## Implementation notes

* The function `G` is defined on all of `ℝ`; only its values on `(0, 1/2)` enter the
  hypotheses and the conclusion.
* The blueprint takes `p` an odd prime and `r ≥ 1`. Neither hypothesis is needed: for every
  natural number `p` the integers `1 ≤ a ≤ (p - 1)/2` are exactly those with `0 < a/p < 1/2`
  (and for `p = 0` both sides vanish), and for `r = 0` the partition is degenerate.
* Sample points are indexed by integers `a` in an arbitrary finset `F` containing every `a`
  with `a/p` in the relevant interval, and the step function is replaced by its indicator on
  that interval; this makes the estimate additive over adjacent intervals.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2: the step structure of the pole counts.
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set
open scoped Interval

/-- On an interval `(u, v)` where `G` is constant and bounded by `C`, the sum of `G (a / p)`
over the integers `a` with `a / p ∈ (u, v)` differs from `p ∫_u^v G` by at most `C`; moreover
`G` is interval integrable on `[u, v]`. -/
theorem abs_sum_indicator_Ioo_sub_integral_le {p u v c C : ℝ} (hp : 0 < p) (huv : u < v)
    (F : Finset ℤ) {G : ℝ → ℝ} (hG : ∀ x ∈ Ioo u v, G x = c)
    (hGC : ∀ x ∈ Ioo u v, |G x| ≤ C) (hF : ∀ a : ℤ, (a : ℝ) / p ∈ Ioo u v → a ∈ F) :
    IntervalIntegrable G volume u v ∧
      |∑ a ∈ F, (Ioo u v).indicator G (a / p) - p * ∫ x in u..v, G x| ≤ C := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι u v → G x = c := by
    filter_upwards [Measure.ae_ne volume v] with x hx hxI
    rw [uIoc_of_le huv.le] at hxI
    exact hG x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩
  have hmid : (u + v) / 2 ∈ Ioo u v := ⟨by linarith, by linarith⟩
  have hc : |c| ≤ C := hG _ hmid ▸ hGC _ hmid
  refine ⟨(intervalIntegrable_const (c := c)).congr_ae ?_, ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with x hx hxI using (hx hxI).symm
  have hsum : ∑ a ∈ F, (Ioo u v).indicator G (a / p) =
      (Finset.Ioo ⌊p * u⌋ ⌈p * v⌉).card * c := by
    have hfilt : F.filter (fun a : ℤ => (a : ℝ) / p ∈ Ioo u v) =
        Finset.Ioo ⌊p * u⌋ ⌈p * v⌉ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Ioo, mem_Ioo, Int.floor_lt, Int.lt_ceil,
        lt_div_iff₀ hp, div_lt_iff₀ hp]
      exact ⟨fun ⟨_, h1, h2⟩ => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ =>
        ⟨hF a ⟨(lt_div_iff₀ hp).2 (by linarith), (div_lt_iff₀ hp).2 (by linarith)⟩,
          by linarith, by linarith⟩⟩
    rw [← hfilt, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [indicator_apply]
    split_ifs with h
    · simp [hG _ h]
    · simp
  have hint : ∫ x in u..v, G x = (v - u) * c := by
    rw [intervalIntegral.integral_congr_ae hae]
    simp
  have hcard : ((Finset.Ioo ⌊p * u⌋ ⌈p * v⌉).card : ℝ) = ⌈p * v⌉ - ⌊p * u⌋ - 1 := by
    have hlt : ⌊p * u⌋ < ⌈p * v⌉ := by
      rw [Int.floor_lt]
      exact (mul_lt_mul_of_pos_left huv hp).trans_le (Int.le_ceil _)
    rw [Int.card_Ioo]
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌈p * v⌉ - ⌊p * u⌋ - 1 by omega)
  rw [hsum, hint, hcard]
  have hb : |((⌈p * v⌉ : ℝ) - ⌊p * u⌋ - 1) - p * (v - u)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Int.le_ceil (p * v), Int.ceil_lt_add_one (p * v),
      Int.floor_le (p * u), Int.sub_one_lt_floor (p * u)]
  calc |((⌈p * v⌉ : ℝ) - ⌊p * u⌋ - 1) * c - p * ((v - u) * c)|
      = |c| * |((⌈p * v⌉ : ℝ) - ⌊p * u⌋ - 1) - p * (v - u)| := by
        rw [← abs_mul]; ring_nf
    _ ≤ C * 1 := mul_le_mul hc hb (abs_nonneg _) ((abs_nonneg _).trans hc)
    _ = C := mul_one C

/-- At most one integer `a` has `a / p = m`, so if `G` is bounded by `C ≥ 0` on `T`, the sum of
the indicator of `{m} ∩ T` against `G` over the sample points `a / p` is bounded by `C`. -/
theorem abs_sum_indicator_singleton_inter_le {p m C : ℝ} (hp : p ≠ 0) (hC : 0 ≤ C)
    (F : Finset ℤ) {G : ℝ → ℝ} {T : Set ℝ} (hGC : ∀ x ∈ T, |G x| ≤ C) :
    |∑ a ∈ F, ({m} ∩ T).indicator G (a / p)| ≤ C := by
  classical
  have hle : ∀ x, |({m} ∩ T).indicator G x| ≤ C := fun x => by
    rw [indicator_apply]
    split_ifs with h
    · exact hGC x h.2
    · simpa using hC
  by_cases h : ∃ a ∈ F, (a : ℝ) / p = m
  · obtain ⟨a, ha, ham⟩ := h
    rw [Finset.sum_eq_single a (fun b _ hba => ?_) (fun h => absurd ha h)]
    · exact hle _
    · refine indicator_of_notMem (fun hb => hba ?_) _
      exact_mod_cast (div_left_inj' hp).1 (hb.1.trans ham.symm)
  · push Not at h
    rw [Finset.sum_eq_zero fun a ha => indicator_of_notMem (fun h' => h a ha h'.1) _]
    simpa using hC

/-- **Riemann sums of step functions.** Let `z₀ < z₁ < ⋯ < z_r` and let `G` equal `c_k` on
each `(z_{k-1}, z_k)` and be bounded by `C ≥ 0` on `(z₀, z_r)`. Then `G` is interval integrable
on `[z₀, z_r]`, and the sum of `G (a / p)` over the integers `a` with `a / p ∈ (z₀, z_r)`
differs from `p ∫_{z₀}^{z_r} G` by at most `2 r C`. -/
theorem abs_sum_indicator_sub_integral_le_of_step {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (F : Finset ℤ) {G : ℝ → ℝ} {r : ℕ} (z : Fin (r + 1) → ℝ) (hz : StrictMono z)
    (c : Fin r → ℝ) (hG : ∀ k : Fin r, ∀ x ∈ Ioo (z k.castSucc) (z k.succ), G x = c k)
    (hGC : ∀ x ∈ Ioo (z 0) (z (Fin.last r)), |G x| ≤ C)
    (hF : ∀ a : ℤ, (a : ℝ) / p ∈ Ioo (z 0) (z (Fin.last r)) → a ∈ F) :
    IntervalIntegrable G volume (z 0) (z (Fin.last r)) ∧
      |∑ a ∈ F, (Ioo (z 0) (z (Fin.last r))).indicator G (a / p) -
        p * ∫ x in z 0..z (Fin.last r), G x| ≤ 2 * r * C := by
  induction r with
  | zero => simp
  | succ r ih =>
    set m := z (Fin.last r).castSucc with hm
    have hzm : z 0 ≤ m := hz.monotone (Fin.zero_le _)
    have hml : m < z (Fin.last (r + 1)) := hz (Fin.castSucc_lt_last _)
    have hsub : Ioo (z 0) m ⊆ Ioo (z 0) (z (Fin.last (r + 1))) :=
      Ioo_subset_Ioo_right hml.le
    have hsub' : Ioo m (z (Fin.last (r + 1))) ⊆ Ioo (z 0) (z (Fin.last (r + 1))) :=
      Ioo_subset_Ioo_left hzm
    obtain ⟨hI1, hE1⟩ := ih (z ∘ Fin.castSucc) (hz.comp Fin.strictMono_castSucc)
      (c ∘ Fin.castSucc) (fun k x hx => by simpa using hG k.castSucc x (by simpa using hx))
      (fun x hx => hGC x (hsub hx)) (fun a ha => hF a (hsub ha))
    simp only [Function.comp_apply, Fin.castSucc_zero] at hI1 hE1
    rw [← hm] at hI1 hE1
    have hlast := hG (Fin.last r)
    rw [Fin.succ_last] at hlast
    obtain ⟨hI2, hE2⟩ := abs_sum_indicator_Ioo_sub_integral_le hp hml F hlast
      (fun x hx => hGC x (hsub' hx)) (fun a ha => hF a (hsub' ha))
    have hE3 := abs_sum_indicator_singleton_inter_le (m := m) hp.ne' hC F hGC
    refine ⟨hI1.trans hI2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    have hind : ∀ x, (Ioo (z 0) (z (Fin.last (r + 1)))).indicator G x =
        (Ioo (z 0) m).indicator G x +
          ({m} ∩ Ioo (z 0) (z (Fin.last (r + 1)))).indicator G x +
          (Ioo m (z (Fin.last (r + 1)))).indicator G x := fun x => by
      simp only [indicator_apply, mem_Ioo, mem_inter_iff, mem_singleton_iff]
      rcases lt_trichotomy x m with h | h | h
      · simp [h, h.ne, not_lt.2 h.le, h.trans hml]
      · subst h; simp
      · simp [h, h.ne', not_lt.2 h.le, hzm.trans_lt h]
    simp only [hind, Finset.sum_add_distrib]
    calc _ = |(∑ a ∈ F, (Ioo (z 0) m).indicator G (a / p) - p * ∫ x in z 0..m, G x) +
          ∑ a ∈ F, ({m} ∩ Ioo (z 0) (z (Fin.last (r + 1)))).indicator G (a / p) +
          (∑ a ∈ F, (Ioo m (z (Fin.last (r + 1)))).indicator G (a / p) -
            p * ∫ x in m..z (Fin.last (r + 1)), G x)| := by
          congr 1; ring
      _ ≤ 2 * r * C + C + C := (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add hE1 hE3)) hE2)
      _ = 2 * ↑(r + 1) * C := by push_cast; ring

/-- **The step structure of the pole counts.** Let `0 = z₀ < z₁ < ⋯ < z_r = 1/2`, let `G` equal
`c_k` on each `(z_{k-1}, z_k)`, and let `|G| ≤ C` on `(0, 1/2)`, where `C ≥ 0`. Then
`|∑_{a=1}^{(p-1)/2} G(a/p) - p ∫_0^{1/2} G| ≤ 2 r C`.

The blueprint states this for `p` an odd prime and `r ≥ 1`; it holds for every natural
number `p` and every `r`. -/
@[zeta5irr "lem_norm_step_riemann"]
theorem abs_sum_step_sub_integral_le (p r : ℕ) (z : Fin (r + 1) → ℝ) (hz : StrictMono z)
    (hz0 : z 0 = 0) (hzr : z (Fin.last r) = 1 / 2) (c : Fin r → ℝ) {C : ℝ} (hC : 0 ≤ C)
    {G : ℝ → ℝ} (hG : ∀ k : Fin r, ∀ x ∈ Ioo (z k.castSucc) (z k.succ), G x = c k)
    (hGC : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), |G x| ≤ C) :
    |∑ a ∈ Finset.Icc 1 ((p - 1) / 2), G (a / p) - p * ∫ x in (0 : ℝ)..1 / 2, G x| ≤
      2 * r * C := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simpa using by positivity
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hmem : ∀ n ∈ Finset.Icc 1 ((p - 1) / 2), ((n : ℤ) : ℝ) / p ∈ Ioo (0 : ℝ) (1 / 2) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have h2 : (2 * n + 1 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 * n + 1 ≤ p)
    push_cast
    exact ⟨by positivity, by rw [div_lt_iff₀ hp']; linarith⟩
  obtain ⟨-, h⟩ := abs_sum_indicator_sub_integral_le_of_step hp' hC
    ((Finset.Icc 1 ((p - 1) / 2)).map Nat.castEmbedding) z hz c hG (by rwa [hz0, hzr])
    (fun a ha => by
      rw [hz0, hzr, mem_Ioo, lt_div_iff₀ hp', div_lt_iff₀ hp'] at ha
      have h1 : (0 : ℤ) < a := by exact_mod_cast (by linarith : (0 : ℝ) < a)
      have h2 : 2 * a < p := by exact_mod_cast (by linarith : (2 * a : ℝ) < p)
      refine Finset.mem_map.2 ⟨a.toNat, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
      simp [h1.le])
  rw [hz0, hzr, Finset.sum_map] at h
  convert h using 3
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Nat.castEmbedding_apply, indicator_of_mem (hmem n hn)]
  simp

end Zeta5Irr
