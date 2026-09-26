/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormPwc
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

/-!
# Step-function sandwiches of piecewise continuous functions

Let `f` be piecewise continuous on `[u, v]` and let `ε > 0`. Then there is a partition
`u = u₀ < u₁ < ⋯ < u_r = v`, `r ≥ 1`, and reals `c_k⁻ ≤ c_k⁺` bounding `f` below and above on
each open piece `(u_{k-1}, u_k)`, such that the total oscillation
`∑_k (c_k⁺ - c_k⁻) (u_k - u_{k-1})` of the two step functions is at most `ε`.

Each continuous piece `g_j` of `f` is uniformly continuous on its closed interval, so a uniform
subdivision of that interval of fine enough mesh makes the oscillation of `g_j` on every
subinterval at most `ε / (v - u)`; concatenating these subdivisions over all pieces gives a
partition of `[u, v]` of total oscillation at most `ε`.

## Main results

* `Zeta5Irr.PiecewiseContinuousOn.exists_step_sandwich`: the step-function sandwich.

## Implementation notes

* During the construction, partitions are indexed by `ℕ` rather than by `Fin (r + 1)`, so that
  two partitions of adjacent intervals can be concatenated by a case split on the index; the
  final statement is in the `Fin` form of `Zeta5Irr.PiecewiseContinuousOn`.
* On each subinterval `[a, b]` of the uniform subdivision the bounds taken are
  `g(a) ∓ ε / (2 (v - u))` instead of the minimum and maximum of `g` on `[a, b]`; the
  oscillation estimate is the same.
* The hypothesis `u < v` of the source follows from piecewise continuity.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.6: piecewise continuity.
-/

@[expose] public section

namespace Zeta5Irr

open Set

/-- `f` admits, on `[a, b]`, a partition indexed by `ℕ` with lower and upper step bounds on the
open pieces whose total oscillation is at most `e`. -/
private def StepSandwich (f : ℝ → ℝ) (a b e : ℝ) : Prop :=
  ∃ (n : ℕ) (q cm cp : ℕ → ℝ), 0 < n ∧ q 0 = a ∧ q n = b ∧ (∀ i < n, q i < q (i + 1)) ∧
    (∀ i < n, ∀ t ∈ Ioo (q i) (q (i + 1)), cm i ≤ f t ∧ f t ≤ cp i) ∧
    ∑ i ∈ Finset.range n, (cp i - cm i) * (q (i + 1) - q i) ≤ e

variable {f : ℝ → ℝ} {u v : ℝ}

private lemma StepSandwich.mono {a b e e' : ℝ} (h : StepSandwich f a b e) (he : e ≤ e') :
    StepSandwich f a b e' := by
  obtain ⟨n, q, cm, cp, hn, h0, hn', hq, hb, hs⟩ := h
  exact ⟨n, q, cm, cp, hn, h0, hn', hq, hb, hs.trans he⟩

private lemma StepSandwich.append {a m b e₁ e₂ : ℝ} (h₁ : StepSandwich f a m e₁)
    (h₂ : StepSandwich f m b e₂) : StepSandwich f a b (e₁ + e₂) := by
  obtain ⟨n, q, cm, cp, hn, h0, hn', hq, hb, hs⟩ := h₁
  obtain ⟨n', q', cm', cp', hn₂, h0', hn'', hq', hb', hs'⟩ := h₂
  let Q : ℕ → ℝ := fun i => if i ≤ n then q i else q' (i - n)
  let CM : ℕ → ℝ := fun i => if i < n then cm i else cm' (i - n)
  let CP : ℕ → ℝ := fun i => if i < n then cp i else cp' (i - n)
  have hQ1 : ∀ i ≤ n, Q i = q i := fun i hi => by simp [Q, hi]
  have hQ2 : ∀ i, Q (n + i) = q' i := fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [Q, hn', h0']
    · simp [Q, show ¬ n + i ≤ n by omega]
  have hCM1 : ∀ i < n, CM i = cm i := fun i hi => by simp [CM, hi]
  have hCM2 : ∀ i, CM (n + i) = cm' i := fun i => by simp [CM]
  have hCP1 : ∀ i < n, CP i = cp i := fun i hi => by simp [CP, hi]
  have hCP2 : ∀ i, CP (n + i) = cp' i := fun i => by simp [CP]
  refine ⟨n + n', Q, CM, CP, by omega, by rw [hQ1 0 (Nat.zero_le _), h0],
    by rw [hQ2, hn''], ?_, ?_, ?_⟩
  · intro i hi
    rcases lt_or_ge i n with h | h
    · rw [hQ1 i h.le, hQ1 (i + 1) h]
      exact hq i h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_assoc, hQ2, hQ2]
      exact hq' j (by omega)
  · intro i hi t ht
    rcases lt_or_ge i n with h | h
    · rw [hQ1 i h.le, hQ1 (i + 1) h] at ht
      rw [hCM1 i h, hCP1 i h]
      exact hb i h t ht
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_assoc, hQ2, hQ2] at ht
      rw [hCM2, hCP2]
      exact hb' j (by omega) t ht
  · rw [Finset.sum_range_add]
    refine add_le_add (le_of_eq_of_le (Finset.sum_congr rfl fun i hi => ?_) hs)
      (le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) hs')
    · have hi := Finset.mem_range.1 hi
      rw [hCM1 i hi, hCP1 i hi, hQ1 i hi.le, hQ1 (i + 1) hi]
    · rw [hCM2, hCP2, add_assoc, hQ2, hQ2]

/-- A function agreeing on `(a, b)` with a function continuous on `[a, b]` admits a step
sandwich on `[a, b]` with every piece of oscillation at most `δ`. -/
private lemma stepSandwich_of_continuousOn {g : ℝ → ℝ} {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hg : ContinuousOn g (Icc a b)) (hfg : EqOn f g (Ioo a b)) :
    StepSandwich f a b (δ * (b - a)) := by
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) (δ / 2) (half_pos hδ)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / η)
  have hN0 : (0 : ℝ) < N := (div_pos (sub_pos.2 hab) hη).trans hN
  set h := (b - a) / N with hh_def
  have hh : 0 < h := div_pos (sub_pos.2 hab) hN0
  have hNh : N * h = b - a := by rw [hh_def]; field_simp
  have hhη : h ≤ η := by
    rw [div_lt_iff₀ hη] at hN
    rw [hh_def, div_le_iff₀ hN0]
    linarith
  refine ⟨N, fun i => a + i * h, fun i => g (a + i * h) - δ / 2,
    fun i => g (a + i * h) + δ / 2, by exact_mod_cast hN0, by simp, by simp [hNh], ?_, ?_, ?_⟩
  · intro i _
    push_cast
    linarith
  · intro i hi t ht
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
    push_cast at ht
    have hx : a + i * h ∈ Icc a b := ⟨by nlinarith, by nlinarith⟩
    have ht' : t ∈ Icc a b := ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    have hd := hgη t ht' _ hx (by rw [Real.dist_eq, abs_le]; constructor <;> nlinarith [ht.1, ht.2])
    rw [Real.dist_eq, abs_le] at hd
    rw [hfg ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩]
    constructor <;> linarith [hd.1, hd.2]
  · refine le_of_eq ?_
    rw [Finset.sum_congr rfl fun (i : ℕ) _ => show
      (g (a + (i : ℝ) * h) + δ / 2 - (g (a + i * h) - δ / 2)) *
        (a + ((i + 1 : ℕ) : ℝ) * h - (a + i * h)) = δ * h by push_cast; ring]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hNh]
    ring

/-- **Step-function sandwich.** Let `f` be piecewise continuous on `[u, v]` and let `ε > 0`.
Then there are a partition `u = q 0 < q 1 < ⋯ < q r = v` with `r ≥ 1` and reals `cm k`, `cp k`
with `cm k ≤ f t ≤ cp k` for every `t` in the `k`-th open piece `(q k, q (k + 1))`, such that
`∑_k (cp k - cm k) (q (k + 1) - q k) ≤ ε`. -/
@[zeta5irr "lem_norm_step_sandwich"]
theorem PiecewiseContinuousOn.exists_step_sandwich (hf : PiecewiseContinuousOn f u v) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (r : ℕ) (q : Fin (r + 1) → ℝ) (cm cp : Fin r → ℝ), 0 < r ∧ StrictMono q ∧ q 0 = u ∧
      q (Fin.last r) = v ∧
      (∀ k : Fin r, ∀ t ∈ Ioo (q k.castSucc) (q k.succ), cm k ≤ f t ∧ f t ≤ cp k) ∧
      ∑ k, (cp k - cm k) * (q k.succ - q k.castSucc) ≤ ε := by
  have huv := hf.lt
  obtain ⟨r, p, hr, hp, hp0, hpr, -, hg⟩ := hf
  set δ := ε / (v - u) with hδ_def
  have hδ : 0 < δ := div_pos hε (sub_pos.2 huv)
  have key : ∀ j (hj : j < r),
      StepSandwich f u (p ⟨j + 1, by omega⟩) (δ * (p ⟨j + 1, by omega⟩ - u)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      obtain ⟨g, hgc, hfg⟩ := hg ⟨0, hj⟩
      have : StepSandwich f (p ⟨0, by omega⟩) (p ⟨0 + 1, by omega⟩)
          (δ * (p ⟨0 + 1, by omega⟩ - p ⟨0, by omega⟩)) :=
        stepSandwich_of_continuousOn (hp (Fin.mk_lt_mk.2 (by omega))) hδ hgc hfg
      change StepSandwich f (p 0) _ (δ * (_ - p 0)) at this
      rwa [hp0] at this
    | succ j ih =>
      intro hj
      obtain ⟨g, hgc, hfg⟩ := hg ⟨j + 1, hj⟩
      have h2 : StepSandwich f (p ⟨j + 1, by omega⟩) (p ⟨j + 1 + 1, by omega⟩)
          (δ * (p ⟨j + 1 + 1, by omega⟩ - p ⟨j + 1, by omega⟩)) :=
        stepSandwich_of_continuousOn (hp (Fin.mk_lt_mk.2 (by omega))) hδ hgc hfg
      exact ((ih (by omega)).append h2).mono (le_of_eq (by ring))
  have hlast : (⟨r - 1 + 1, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp; omega)
  have hS := key (r - 1) (by omega)
  rw [hlast, hpr, hδ_def, div_mul_cancel₀ _ (sub_pos.2 huv).ne'] at hS
  obtain ⟨n, q, cm, cp, hn, h0, hn', hq, hb, hs⟩ := hS
  refine ⟨n, fun i => q i, fun i => cm i, fun i => cp i, hn,
    Fin.strictMono_iff_lt_succ.2 fun i => hq i i.2, h0, hn', fun k t ht => hb k k.2 t ht, ?_⟩
  refine le_of_eq_of_le ?_ hs
  rw [← Fin.sum_univ_eq_sum_range (fun i => (cp i - cm i) * (q (i + 1) - q i)) n]
  simp

end Zeta5Irr
