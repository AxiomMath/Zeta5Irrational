/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormPwc
public import Zeta5Irr.PrimeSum.NormStepSandwich
public import Zeta5Irr.PrimeSum.NormThetaInterval
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Prime sums in the outer variable

Let `0 ≤ u` and let `f` be piecewise continuous on `[u, v]`. Then
`(1 / K) ∑_{uK < p ≤ vK} f(p / K) log p → ∫_u^v f(y) dy` as `K → ∞`, the sum being over
primes.

Given `ε > 0`, sandwich `f` between step functions `c_k⁻ ≤ f ≤ c_k⁺` on the open pieces
`(u_{k-1}, u_k)` of a partition of `[u, v]` whose total oscillation is at most `ε`. On each
half-open piece `(u_{k-1}, u_k]` the prime number theorem gives
`(1 / K) ∑_{u_{k-1}K < p ≤ u_kK} log p → u_k - u_{k-1}`. The at most one prime with
`p / K = u_k` contributes at most `C log (vK)`, `C` a bound for `f`, which is `o(K)`.
Hence the weighted sum is eventually within `2 ε` of the integral, which the two step sums
enclose.

## Main results

* `Zeta5Irr.eventually_sum_prime_mul_log_div_lt`: the upper step bound for the weighted prime
  sum.
* `Zeta5Irr.PiecewiseContinuousOn.tendsto_sum_prime_mul_log_div_atTop`: the limit.

## Implementation notes

* As in `Zeta5Irr.tendsto_sum_Ioc_prime_log_div_atTop`, the primes `uK < p ≤ vK` are those
  of `Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊`, and `K` is a real parameter tending to `∞`.
* The source assumes `0 < u < v`; the statement here needs only `0 ≤ u`, the inequality
  `u < v` being part of piecewise continuity.
* The lower bound is obtained from the upper bound applied to `-f`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.7 (The prime number theorem).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology Set MeasureTheory

variable {f : ℝ → ℝ}

/-- For any `q : Fin (r + 1) → ℝ`, a point of `(q 0, q r]` lies in one of the half-open pieces
`(q (k - 1), q k]`. -/
theorem exists_fin_mem_Ioc_castSucc_succ {r : ℕ} (q : Fin (r + 1) → ℝ) {t : ℝ}
    (ht : t ∈ Ioc (q 0) (q (Fin.last r))) :
    ∃ k : Fin r, t ∈ Ioc (q k.castSucc) (q k.succ) := by
  induction r with
  | zero => exact absurd ht (by simp)
  | succ r ih =>
    by_cases h : t ≤ q (Fin.last r).castSucc
    · obtain ⟨k, hk⟩ := ih (q ∘ Fin.castSucc) ⟨by simpa using ht.1, by simpa using h⟩
      exact ⟨k.castSucc, by simpa using hk⟩
    · exact ⟨Fin.last r, lt_of_not_ge h, by simpa using ht.2⟩

/-- The integral over `[q 0, q r]` is the sum of the integrals over the pieces
`[q (k - 1), q k]` of `q : Fin (r + 1) → ℝ`. -/
theorem integral_eq_sum_fin_pieces {r : ℕ} (q : Fin (r + 1) → ℝ)
    (h : ∀ k : Fin r, IntervalIntegrable f volume (q k.castSucc) (q k.succ)) :
    ∫ x in q 0..q (Fin.last r), f x = ∑ k : Fin r, ∫ x in q k.castSucc..q k.succ, f x := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 := ih (q ∘ Fin.castSucc) fun k => by simpa using h k.castSucc
    have hI := intervalIntegrable_of_fin_pieces (q ∘ Fin.castSucc) fun k => by
      simpa using h k.castSucc
    have h2 := h (Fin.last r)
    simp only [Function.comp_apply, Fin.castSucc_zero] at h1 hI
    rw [Fin.succ_last] at h2
    simp only [Fin.castSucc_succ] at h1
    rw [Fin.sum_univ_castSucc, ← h1, Fin.succ_last,
      intervalIntegral.integral_add_adjacent_intervals hI h2]

/-- If `c k ≤ f` on the open pieces `(q (k - 1), q k)` of a partition `q` and `f` is interval
integrable on `[q 0, q r]`, then the lower step sum `∑_k c k (q k - q (k - 1))` is at most
`∫_{q 0}^{q r} f`. -/
theorem sum_mul_le_integral_of_fin_pieces {r : ℕ} (q : Fin (r + 1) → ℝ) (hq : StrictMono q)
    (c : Fin r → ℝ) (hint : IntervalIntegrable f volume (q 0) (q (Fin.last r)))
    (hc : ∀ k : Fin r, ∀ t ∈ Ioo (q k.castSucc) (q k.succ), c k ≤ f t) :
    ∑ k, c k * (q k.succ - q k.castSucc) ≤ ∫ x in q 0..q (Fin.last r), f x := by
  have hpc : ∀ k : Fin r, IntervalIntegrable f volume (q k.castSucc) (q k.succ) := fun k =>
    hint.mono_set (by
      rw [uIcc_of_le (hq.monotone k.castSucc_le_succ),
        uIcc_of_le (hq.monotone (Fin.zero_le _))]
      exact Icc_subset_Icc (hq.monotone (Fin.zero_le _)) (hq.monotone (Fin.le_last _)))
  rw [integral_eq_sum_fin_pieces q hpc]
  refine Finset.sum_le_sum fun k _ => ?_
  calc c k * (q k.succ - q k.castSucc) = ∫ _ in q k.castSucc..q k.succ, c k := by
        simp [mul_comm]
    _ ≤ ∫ x in q k.castSucc..q k.succ, f x := by
        refine intervalIntegral.integral_mono_ae_restrict (hq.monotone k.castSucc_le_succ)
          intervalIntegrable_const (hpc k) ?_
        refine (ae_restrict_iff' measurableSet_Icc).2 ?_
        filter_upwards [Measure.ae_ne volume (q k.castSucc), Measure.ae_ne volume (q k.succ)]
          with x h1 h2 hx
        exact hc k x ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), lt_of_le_of_ne hx.2 h2⟩

/-- For `K > 0` and `0 ≤ x ≤ y`, a natural number `p` satisfies `⌊xK⌋₊ < p ≤ ⌊yK⌋₊` exactly
when `p / K ∈ (x, y]`. -/
theorem mem_Ioc_floor_mul_iff {x y K : ℝ} (hK : 0 < K) (hx : 0 ≤ x) (hxy : x ≤ y) (p : ℕ) :
    p ∈ Finset.Ioc ⌊x * K⌋₊ ⌊y * K⌋₊ ↔ (p : ℝ) / K ∈ Ioc x y := by
  rw [Finset.mem_Ioc, Nat.floor_lt (mul_nonneg hx hK.le),
    Nat.le_floor_iff (mul_nonneg (hx.trans hxy) hK.le), mem_Ioc, lt_div_iff₀ hK,
    div_le_iff₀ hK]

/-- Restricting the sum over primes `uK < p ≤ vK` to those with `p / K ∈ (a, b]`,
`u ≤ a ≤ b ≤ v`, gives the sum over primes `aK < p ≤ bK`. -/
theorem sum_prime_indicator_Ioc {u a b v K : ℝ} (hK : 0 < K) (hu : 0 ≤ u) (hua : u ≤ a)
    (hab : a ≤ b) (hbv : b ≤ v) (g : ℝ → ℝ) :
    ∑ p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime,
        (Ioc a b).indicator g (p / K) * Real.log p =
      ∑ p ∈ Finset.Ioc ⌊a * K⌋₊ ⌊b * K⌋₊ with p.Prime, g (p / K) * Real.log p := by
  simp only [indicator_apply, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, mem_Ioc_floor_mul_iff hK hu (hua.trans (hab.trans hbv)),
    mem_Ioc_floor_mul_iff hK (hu.trans hua) hab]
  constructor
  · rintro ⟨⟨-, hp⟩, h⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨⟨hua.trans_lt h.1, h.2.trans hbv⟩, hp⟩, h⟩

/-- At most one sample point `p / K` equals `x`, so a point mass `B ≥ 0` at `x` contributes at
most `B log (vK)` to a sum over `1 ≤ p ≤ vK`. -/
theorem sum_indicator_singleton_mul_log_le {s : Finset ℕ} {K B x v : ℝ} (hK : 0 < K)
    (hB : 0 ≤ B) (hs : ∀ p ∈ s, 1 ≤ p ∧ (p : ℝ) ≤ v * K) (hv : 1 ≤ v * K) :
    ∑ p ∈ s, ({x} : Set ℝ).indicator (fun _ => B) (p / K) * Real.log p ≤
      B * Real.log (v * K) := by
  by_cases h : ∃ p ∈ s, (p : ℝ) / K = x
  · obtain ⟨p, hp, hpx⟩ := h
    rw [Finset.sum_eq_single p]
    · rw [indicator_of_mem (by simpa using hpx)]
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hs p hp).1
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (hs p hp).2) hB
    · intro b _ hbp
      rw [indicator_of_notMem, zero_mul]
      intro hb
      refine hbp ?_
      have : (b : ℝ) / K = p / K := (hb : (b : ℝ) / K = x).trans hpx.symm
      exact_mod_cast (div_left_inj' hK.ne').1 this
    · exact fun h => absurd hp h
  · push Not at h
    rw [Finset.sum_eq_zero fun p hp => by
      rw [indicator_of_notMem (show (p : ℝ) / K ∉ ({x} : Set ℝ) from h p hp), zero_mul]]
    exact mul_nonneg hB (Real.log_nonneg hv)

/-- A function bounded above by `c k` on the open pieces `(q (k - 1), q k)` of a partition and by
`C ≤ c k + B` on `(q 0, q r]` is bounded on `(q 0, q r]` by the step function equal to `c k` on
the half-open pieces `(q (k - 1), q k]`, plus point masses `B ≥ 0` at the break points. -/
theorem le_sum_indicator_Ioc_add_sum_indicator_singleton {r : ℕ} (q : Fin (r + 1) → ℝ)
    (hq : StrictMono q) (c : Fin r → ℝ) {C B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, C ≤ c k + B)
    (hc : ∀ k : Fin r, ∀ t ∈ Ioo (q k.castSucc) (q k.succ), f t ≤ c k)
    (hC : ∀ t ∈ Ioc (q 0) (q (Fin.last r)), f t ≤ C) {t : ℝ}
    (ht : t ∈ Ioc (q 0) (q (Fin.last r))) :
    f t ≤ ∑ k : Fin r, (Ioc (q k.castSucc) (q k.succ)).indicator (fun _ => c k) t +
      ∑ k : Fin r, ({q k.succ} : Set ℝ).indicator (fun _ => B) t := by
  obtain ⟨k₀, hk₀⟩ := exists_fin_mem_Ioc_castSucc_succ q ht
  have h1 : ∑ k : Fin r, (Ioc (q k.castSucc) (q k.succ)).indicator (fun _ => c k) t = c k₀ := by
    rw [Finset.sum_eq_single k₀ (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ _) h),
      indicator_of_mem hk₀]
    refine indicator_of_notMem (fun hjt => ?_) _
    rcases lt_or_gt_of_ne hj with h | h
    · have : q j.succ ≤ q k₀.castSucc := hq.monotone (Fin.succ_le_castSucc_iff.2 h)
      linarith [hjt.2, hk₀.1]
    · have : q k₀.succ ≤ q j.castSucc := hq.monotone (Fin.succ_le_castSucc_iff.2 h)
      linarith [hjt.1, hk₀.2]
  have h2 : 0 ≤ ∑ k : Fin r, ({q k.succ} : Set ℝ).indicator (fun _ => B) t :=
    Finset.sum_nonneg fun k _ => indicator_nonneg (fun _ _ => hB0) _
  rw [h1]
  rcases hk₀.2.lt_or_eq with h | h
  · linarith [hc k₀ t ⟨hk₀.1, h⟩]
  · have h3 : B ≤ ∑ k : Fin r, ({q k.succ} : Set ℝ).indicator (fun _ => B) t := by
      refine le_of_eq_of_le ?_ (Finset.single_le_sum
        (f := fun k : Fin r => ({q k.succ} : Set ℝ).indicator (fun _ => B) t)
        (fun k _ => indicator_nonneg (fun _ _ => hB0) _) (Finset.mem_univ k₀))
      simp [h]
    linarith [hC t ht, hB k₀]

/-- **Upper step bound for weighted prime sums.** If `f ≤ c k` on the open pieces of a partition
`0 ≤ q 0 < ⋯ < q r` and `f` is bounded above on `(q 0, q r]`, then for every `δ > 0`,
eventually `(1 / K) ∑_{q₀K < p ≤ q_rK} f(p / K) log p < ∑_k c_k (q k - q (k - 1)) + δ`. -/
theorem eventually_sum_prime_mul_log_div_lt {r : ℕ} (q : Fin (r + 1) → ℝ) (hq : StrictMono q)
    (h0 : 0 ≤ q 0) (c : Fin r → ℝ) {C : ℝ}
    (hc : ∀ k : Fin r, ∀ t ∈ Ioo (q k.castSucc) (q k.succ), f t ≤ c k)
    (hC : ∀ t ∈ Ioc (q 0) (q (Fin.last r)), f t ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K in atTop, (∑ p ∈ Finset.Ioc ⌊q 0 * K⌋₊ ⌊q (Fin.last r) * K⌋₊ with p.Prime,
        f (p / K) * Real.log p) / K < ∑ k, c k * (q k.succ - q k.castSucc) + δ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Eventually.of_forall fun K => by simp [hδ]
  set u := q 0
  set v := q (Fin.last r)
  have huv : u < v := hq (by rw [Fin.lt_def]; simp; omega)
  have hv : 0 < v := h0.trans_lt huv
  have hmono := hq.monotone
  set B := |C| + ∑ k, |c k|
  have hB0 : 0 ≤ B := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hB : ∀ k, C ≤ c k + B := fun k => by
    have := Finset.single_le_sum (f := fun k => |c k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)
    linarith [le_abs_self C, neg_abs_le (c k)]
  have hA : ∀ k : Fin r, Tendsto (fun K : ℝ => (∑ p ∈ Finset.Ioc ⌊q k.castSucc * K⌋₊
      ⌊q k.succ * K⌋₊ with p.Prime, Real.log p) / K) atTop (𝓝 (q k.succ - q k.castSucc)) :=
    fun k => tendsto_sum_Ioc_prime_log_div_atTop (h0.trans (hmono (Fin.zero_le _)))
      (hmono k.castSucc_le_succ)
  have hlog : Tendsto (fun K => Real.log (v * K) / K) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop v⁻¹ 0 1 (inv_ne_zero hv.ne')).comp
      (tendsto_id.const_mul_atTop hv)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    simp only [Function.comp_apply, id, pow_one, add_zero]
    field_simp
  have hlim := (tendsto_finsetSum Finset.univ fun k _ => (hA k).const_mul (c k)).add
    (hlog.const_mul ((r : ℝ) * B))
  rw [mul_zero, add_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hδ)),
    eventually_gt_atTop 0, eventually_ge_atTop v⁻¹] with K hK1 hK hKv
  refine lt_of_le_of_lt ?_ hK1
  have hvK : 1 ≤ v * K := by
    have := mul_le_mul_of_nonneg_left hKv hv.le
    rwa [mul_inv_cancel₀ hv.ne'] at this
  have hP : ∀ p ∈ ({p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ | p.Prime} : Finset ℕ),
      (p : ℝ) / K ∈ Ioc u v ∧ 1 ≤ p ∧ (p : ℝ) ≤ v * K := fun p hp => by
    rw [Finset.mem_filter] at hp
    exact ⟨(mem_Ioc_floor_mul_iff hK h0 huv.le p).1 hp.1, hp.2.one_lt.le,
      (Nat.le_floor_iff (by positivity)).1 (Finset.mem_Ioc.1 hp.1).2⟩
  have key : ∑ p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime, f (p / K) * Real.log p ≤
      ∑ k, c k * ∑ p ∈ Finset.Ioc ⌊q k.castSucc * K⌋₊ ⌊q k.succ * K⌋₊ with p.Prime,
        Real.log p + r * B * Real.log (v * K) := by
    calc _ ≤ ∑ p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime,
          (∑ k : Fin r, (Ioc (q k.castSucc) (q k.succ)).indicator (fun _ => c k) (p / K) +
            ∑ k : Fin r, ({q k.succ} : Set ℝ).indicator (fun _ => B) (p / K)) *
              Real.log p := by
          refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
            (le_sum_indicator_Ioc_add_sum_indicator_singleton q hq c hB0 hB hc hC (hP p hp).1)
            (Real.log_nonneg (by exact_mod_cast (hP p hp).2.1))
      _ = ∑ k : Fin r, ∑ p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime,
            (Ioc (q k.castSucc) (q k.succ)).indicator (fun _ => c k) (p / K) * Real.log p +
          ∑ k : Fin r, ∑ p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime,
            ({q k.succ} : Set ℝ).indicator (fun _ => B) (p / K) * Real.log p := by
          simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
          congr 1 <;> exact Finset.sum_comm
      _ ≤ ∑ k, c k * ∑ p ∈ Finset.Ioc ⌊q k.castSucc * K⌋₊ ⌊q k.succ * K⌋₊ with p.Prime,
            Real.log p + ∑ _k : Fin r, B * Real.log (v * K) := by
          refine add_le_add (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
            (Finset.sum_le_sum fun k _ => sum_indicator_singleton_mul_log_le hK hB0
              (fun p hp => (hP p hp).2) hvK)
          rw [sum_prime_indicator_Ioc hK h0 (hmono (Fin.zero_le _)) (hmono k.castSucc_le_succ)
            (hmono (Fin.le_last _)), Finset.mul_sum]
      _ = _ := by simp [mul_assoc]
  calc _ ≤ (∑ k, c k * ∑ p ∈ Finset.Ioc ⌊q k.castSucc * K⌋₊ ⌊q k.succ * K⌋₊ with p.Prime,
        Real.log p + r * B * Real.log (v * K)) / K := div_le_div_of_nonneg_right key hK.le
    _ = _ := by rw [add_div, Finset.sum_div]; simp only [mul_div_assoc]

/-- **Prime sums in the outer variable.** Let `0 ≤ u` and let `f` be piecewise continuous on
`[u, v]`. Then `(1 / K) ∑_{uK < p ≤ vK} f(p / K) log p → ∫_u^v f` as `K → ∞`, the sum being
over primes. -/
@[zeta5irr "lem_norm_pnt_outer"]
theorem PiecewiseContinuousOn.tendsto_sum_prime_mul_log_div_atTop {u v : ℝ} (hu : 0 ≤ u)
    (hf : PiecewiseContinuousOn f u v) :
    Tendsto (fun K : ℝ => (∑ p ∈ Finset.Ioc ⌊u * K⌋₊ ⌊v * K⌋₊ with p.Prime,
      f (p / K) * Real.log p) / K) atTop (𝓝 (∫ y in u..v, f y)) := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hint := hf.intervalIntegrable
  have hCup : ∀ t ∈ Ioc u v, f t ≤ C := fun t ht =>
    (le_abs_self _).trans (hC t (Ioc_subset_Icc_self ht))
  have hClo : ∀ t ∈ Ioc u v, (-f) t ≤ C := fun t ht =>
    (neg_le_abs _).trans (hC t (Ioc_subset_Icc_self ht))
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨r, q, cm, cp, -, hq, rfl, rfl, hb, hs⟩ :=
      hf.exists_step_sandwich (ε := ((∫ y in u..v, f y) - a) / 3) (by linarith)
    have hI := sum_mul_le_integral_of_fin_pieces (f := -f) q hq (fun k => -cp k) hint.neg
      fun k t ht => neg_le_neg (hb k t ht).2
    have hev := eventually_sum_prime_mul_log_div_lt (f := -f) q hq hu (fun k => -cm k)
      (fun k t ht => neg_le_neg (hb k t ht).1) hClo
      (δ := ((∫ y in q 0..q (Fin.last r), f y) - a) / 3) (by linarith)
    simp only [Pi.neg_apply, intervalIntegral.integral_neg, neg_mul,
      Finset.sum_neg_distrib] at hI hev
    simp only [sub_mul] at hs
    rw [Finset.sum_sub_distrib] at hs
    filter_upwards [hev] with K hK
    simp only [neg_div] at hK
    linarith
  · obtain ⟨r, q, cm, cp, -, hq, rfl, rfl, hb, hs⟩ :=
      hf.exists_step_sandwich (ε := (a - ∫ y in u..v, f y) / 3) (by linarith)
    have hI := sum_mul_le_integral_of_fin_pieces q hq cm hint fun k t ht => (hb k t ht).1
    have hev := eventually_sum_prime_mul_log_div_lt q hq hu cp
      (fun k t ht => (hb k t ht).2) hCup
      (δ := (a - ∫ y in q 0..q (Fin.last r), f y) / 3) (by linarith)
    simp only [sub_mul] at hs
    rw [Finset.sum_sub_distrib] at hs
    filter_upwards [hev] with K hK
    linarith

end Zeta5Irr
