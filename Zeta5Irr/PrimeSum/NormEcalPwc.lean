/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormEcal
public import Zeta5Irr.PrimeSum.NormPwc
public import Zeta5Irr.PrimeSum.NormDeltaProd
public import Mathlib.Algebra.Order.Star.Real
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Piecewise continuity of the error term `𝓔`

For all reals `u < v`, the error term `𝓔` of the splitting of the inner limiting function is
piecewise continuous on `[u, v]`.

Each function `t ↦ {c t}` (`c > 0`) is affine between consecutive points of `(2c)⁻¹ ℤ`, and
so is `t ↦ {2 c t}`; between two such points, whether `{c t} < 1/2` is also fixed. By
`integral_ellDeviation_mul_ellDeviation` and `volume_real_normUpperSet_eq`, the two integrals in
`𝓔` are `{2αx}/2 - {2αx}²/2` and `|S(x) ∩ S(αx)| - {2x}{2αx}/2`, and the measure of the
intersection of the two intervals `S(x)`, `S(αx)` is `(min(right ends) - max(left ends))₊`.
So `𝓔(x)` is a continuous function of eight quantities, each of which is bounded and agrees,
away from a finite subset of `[u, v]`, with a continuous function on each open piece.

## Main definitions

* `Zeta5Irr.PiecewiseContinuousOnRefinable`: `f` is bounded on `[u, v]` and there is a finite
  set `D` such that on every open subinterval of `[u, v]` missing `D`, `f` agrees with a
  function continuous on its closure.

## Main results

* `Zeta5Irr.PiecewiseContinuousOnRefinable.comp`: a continuous function of finitely many
  such functions is again such a function.
* `Zeta5Irr.PiecewiseContinuousOnRefinable.piecewiseContinuousOn`: such a function is
  piecewise continuous.
* `Zeta5Irr.volume_real_normUpperSet_inter`: `|S(x₁) ∩ S(x₂)|` as the positive part of the
  difference of the minimal right end and the maximal left end.
* `Zeta5Irr.piecewiseContinuousOn_innerSplitError`: `𝓔` is piecewise continuous on `[u, v]`.

## Implementation notes

* The source states the result for `3 ≤ u < v`. The proof does not use `u ≥ 3`, so the
  lemma is stated for all `u < v`.
* Rather than working with an explicit partition throughout, the proof works with the
  refinable notion `PiecewiseContinuousOnRefinable`, which is stable under continuous
  combinations (take the union of the exceptional sets), and only at the end sorts the
  exceptional set together with `u` and `v` into a partition.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.6 (Piecewise continuity).
-/

@[expose] public section

namespace Zeta5Irr

open Set MeasureTheory

/-- `f` is *refinably piecewise continuous* on `[u, v]`: it is bounded on `[u, v]`, and there is
a finite set `D` such that on every open subinterval `(a, b)` of `[u, v]` missing `D`, the
function `f` agrees with a function continuous on `[a, b]`. -/
def PiecewiseContinuousOnRefinable (f : ℝ → ℝ) (u v : ℝ) : Prop :=
  (∃ C, ∀ t ∈ Icc u v, |f t| ≤ C) ∧ ∃ D : Set ℝ, D.Finite ∧
    ∀ a b, u ≤ a → a < b → b ≤ v → Disjoint (Ioo a b) D →
      ∃ g : ℝ → ℝ, ContinuousOn g (Icc a b) ∧ EqOn f g (Ioo a b)

namespace PiecewiseContinuousOnRefinable

variable {u v : ℝ}

/-- A continuous function of finitely many refinably piecewise continuous functions is
refinably piecewise continuous. -/
theorem comp {ι : Type*} [Finite ι] {f : ι → ℝ → ℝ} {Φ : (ι → ℝ) → ℝ} (hΦ : Continuous Φ)
    (hf : ∀ i, PiecewiseContinuousOnRefinable (f i) u v) :
    PiecewiseContinuousOnRefinable (fun t => Φ (fun i => f i t)) u v := by
  have := Fintype.ofFinite ι
  choose hb D hD h using hf
  choose C hC using hb
  refine ⟨?_, ⋃ i, D i, finite_iUnion hD, fun a b hua hab hbv hDab => ?_⟩
  · obtain ⟨B, hB⟩ :=
      ((isCompact_closedBall (0 : ι → ℝ) (∑ i, |C i|)).image hΦ).isBounded.exists_norm_le
    refine ⟨B, fun t ht => hB _ ⟨fun i => f i t, ?_, rfl⟩⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    exact ((hC i t ht).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))
  · choose g hg hfg using fun i =>
      h i a b hua hab hbv (hDab.mono_right (subset_iUnion D i))
    refine ⟨fun t => Φ (fun i => g i t), hΦ.comp_continuousOn (continuousOn_pi.2 hg), ?_⟩
    intro t ht
    simp only [fun i => hfg i ht]

/-- A refinably piecewise continuous function on `[u, v]`, with `u < v`, is piecewise
continuous there: sort its exceptional points in `(u, v)`, together with `u` and `v`, into a
partition. -/
theorem piecewiseContinuousOn {f : ℝ → ℝ} (hf : PiecewiseContinuousOnRefinable f u v)
    (huv : u < v) : PiecewiseContinuousOn f u v := by
  obtain ⟨hb, D, hD, h⟩ := hf
  obtain ⟨r, p, hr, -, hp, hp0, hpr, hps⟩ := exists_partition_notMem_Ioo huv hD.toFinset
  have hmem : ∀ i, p i ∈ Icc u v := fun i =>
    ⟨hp0 ▸ hp.monotone (Fin.zero_le i), hpr ▸ hp.monotone (Fin.le_last i)⟩
  refine ⟨r, p, hr, hp, hp0, hpr, hb, fun k => ?_⟩
  refine h _ _ (hmem _).1 (hp k.castSucc_lt_succ) (hmem _).2 ?_
  exact Set.disjoint_right.2 fun t htD => hps k t (hD.mem_toFinset.2 htD)

end PiecewiseContinuousOnRefinable

/-- If `c > 0` and `φ` is bounded and agrees with a continuous function on each interval
`(m/2, (m+1)/2)`, `m ∈ ℤ`, then `t ↦ φ (c t)` is refinably piecewise continuous on every
`[u, v]`, the exceptional set being the points of `(2c)⁻¹ ℤ` in `[u, v]`. -/
theorem piecewiseContinuousOnRefinable_comp_mul {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hb : ∃ C, ∀ y, |φ y| ≤ C)
    (hφ : ∀ m : ℤ, ∃ g : ℝ → ℝ, Continuous g ∧ ∀ y, (m : ℝ) < 2 * y → 2 * y < m + 1 →
      φ y = g y)
    (u v : ℝ) : PiecewiseContinuousOnRefinable (fun t => φ (c * t)) u v := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨⟨C, fun t _ => hC _⟩, (fun n : ℤ => (n : ℝ) / (2 * c)) '' Icc ⌈2 * c * u⌉ ⌊2 * c * v⌋,
    (Set.finite_Icc _ _).image _, fun a b hua hab hbv hD => ?_⟩
  have hc2 : 0 < 2 * c := by positivity
  have key : ∀ n : ℤ, a < (n : ℝ) / (2 * c) → (n : ℝ) / (2 * c) < b → False := by
    intro n h₁ h₂
    refine Set.disjoint_left.1 hD ⟨h₁, h₂⟩ ⟨n, Set.mem_Icc.2 ⟨?_, ?_⟩, rfl⟩
    · rw [Int.ceil_le]
      have := (lt_div_iff₀ hc2).1 h₁
      nlinarith
    · rw [Int.le_floor]
      have := (div_lt_iff₀ hc2).1 h₂
      nlinarith
  set m := ⌊c * (a + b)⌋
  have hm₁ : (m : ℝ) ≤ c * (a + b) := Int.floor_le _
  have hm₂ : c * (a + b) < m + 1 := Int.lt_floor_add_one _
  have hlo : ∀ t ∈ Ioo a b, (m : ℝ) < 2 * (c * t) := by
    intro t ht
    by_contra hcon
    rw [not_lt] at hcon
    refine key m ?_ ?_
    · rw [lt_div_iff₀ hc2]; nlinarith [ht.1]
    · rw [div_lt_iff₀ hc2]; nlinarith
  have hhi : ∀ t ∈ Ioo a b, 2 * (c * t) < m + 1 := by
    intro t ht
    by_contra hcon
    rw [not_lt] at hcon
    refine key (m + 1) ?_ ?_
    · rw [lt_div_iff₀ hc2]; push_cast; nlinarith
    · rw [div_lt_iff₀ hc2]; push_cast; nlinarith [ht.2]
  obtain ⟨g, hg, hφg⟩ := hφ m
  exact ⟨fun t => g (c * t), (hg.comp (continuous_const.mul continuous_id)).continuousOn,
    fun t ht => hφg _ (hlo t ht) (hhi t ht)⟩

/-- On `m < 2y < m + 1` with `m = 2j`, `{y} = y - j` and `{y} < 1/2`. -/
theorem fract_eq_sub_of_two_mul_mem_Ioo_even {y : ℝ} {j : ℤ} (h₁ : ((2 * j : ℤ) : ℝ) < 2 * y)
    (h₂ : 2 * y < ((2 * j : ℤ) : ℝ) + 1) : Int.fract y = y - j ∧ Int.fract y < 1 / 2 := by
  push_cast at h₁ h₂
  have : Int.fract y = y - j := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, j, by ring⟩
  exact ⟨this, by rw [this]; linarith⟩

/-- On `m < 2y < m + 1` with `m = 2j + 1`, `{y} = y - j` and `1/2 ≤ {y}`. -/
theorem fract_eq_sub_of_two_mul_mem_Ioo_odd {y : ℝ} {j : ℤ}
    (h₁ : ((2 * j + 1 : ℤ) : ℝ) < 2 * y) (h₂ : 2 * y < ((2 * j + 1 : ℤ) : ℝ) + 1) :
    Int.fract y = y - j ∧ 1 / 2 ≤ Int.fract y := by
  push_cast at h₁ h₂
  have : Int.fract y = y - j := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, j, by ring⟩
  exact ⟨this, by rw [this]; linarith⟩

/-- `S(x)` lies between the open and the closed interval with the same ends. -/
theorem Ioo_subset_normUpperSet_subset_Icc (x : ℝ) :
    Ioo (if Int.fract x < 1 / 2 then 0 else 1 - Int.fract x)
        (if Int.fract x < 1 / 2 then Int.fract x else 1 / 2) ⊆ normUpperSet x ∧
      normUpperSet x ⊆ Icc (if Int.fract x < 1 / 2 then 0 else 1 - Int.fract x)
        (if Int.fract x < 1 / 2 then Int.fract x else 1 / 2) := by
  by_cases h : Int.fract x < 1 / 2
  · simp only [h, ite_true, normUpperSet_of_lt h]
    exact ⟨Ioo_subset_Ioc_self, Ioc_subset_Icc_self⟩
  · simp only [h, ite_false, normUpperSet_of_le (not_lt.1 h)]
    exact ⟨Ioo_subset_Ico_self, Ico_subset_Icc_self⟩

/-- The measure of `S(x₁) ∩ S(x₂)` is `(min(right ends) - max(left ends))₊`, where `S(x)` has
left end `0` or `1 - {x}` and right end `{x}` or `1/2` according as `{x} < 1/2` or not. -/
theorem volume_real_normUpperSet_inter (x₁ x₂ : ℝ) :
    volume.real (normUpperSet x₁ ∩ normUpperSet x₂) =
      (min (if Int.fract x₁ < 1 / 2 then Int.fract x₁ else 1 / 2)
          (if Int.fract x₂ < 1 / 2 then Int.fract x₂ else 1 / 2) -
        max (if Int.fract x₁ < 1 / 2 then 0 else 1 - Int.fract x₁)
          (if Int.fract x₂ < 1 / 2 then 0 else 1 - Int.fract x₂))⁺ := by
  obtain ⟨h₁, h₁'⟩ := Ioo_subset_normUpperSet_subset_Icc x₁
  obtain ⟨h₂, h₂'⟩ := Ioo_subset_normUpperSet_subset_Icc x₂
  have hlo := Set.inter_subset_inter h₁ h₂
  have hhi := Set.inter_subset_inter h₁' h₂'
  rw [Ioo_inter_Ioo] at hlo
  rw [Icc_inter_Icc] at hhi
  have hvol : volume (normUpperSet x₁ ∩ normUpperSet x₂) = ENNReal.ofReal
      (min (if Int.fract x₁ < 1 / 2 then Int.fract x₁ else 1 / 2)
          (if Int.fract x₂ < 1 / 2 then Int.fract x₂ else 1 / 2) -
        max (if Int.fract x₁ < 1 / 2 then 0 else 1 - Int.fract x₁)
          (if Int.fract x₂ < 1 / 2 then 0 else 1 - Int.fract x₂)) := by
    refine le_antisymm ?_ ?_
    · simpa [Real.volume_Icc] using measure_mono (μ := volume) hhi
    · simpa [Real.volume_Ioo] using measure_mono (μ := volume) hlo
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal', posPart_def]

/-- **Piecewise continuity of `𝓔`.** For all reals `u < v` (the source takes `3 ≤ u`), the
error term `𝓔` is piecewise continuous on `[u, v]`. -/
@[zeta5irr "lem_norm_Ecal_pwc"]
theorem piecewiseContinuousOn_innerSplitError {u v : ℝ} (huv : u < v) :
    PiecewiseContinuousOn innerSplitError u v := by
  set L : ℝ → ℝ := fun y => if Int.fract y < 1 / 2 then 0 else 1 - Int.fract y with hL
  set R : ℝ → ℝ := fun y => if Int.fract y < 1 / 2 then Int.fract y else 1 / 2 with hR
  set α : ℝ := (innerRatio : ℝ)
  set f : Fin 8 → ℝ → ℝ := ![fun t => Int.fract (2 * ((heightRatio : ℝ) * t)),
    fun t => Int.fract (2 * (1 * t)), fun t => Int.fract (2 * ((orderRatio : ℝ) * t)),
    fun t => Int.fract (2 * (α * t)), fun t => L (1 * t), fun t => R (1 * t),
    fun t => L (α * t), fun t => R (α * t)] with hf
  set Φ : (Fin 8 → ℝ) → ℝ := fun w =>
    (w 0 * (w 0 - w 1) - (w 0 - w 1)⁺ + w 2 * (1 - w 2)) / 2 + 9 * (w 3 / 2 - w 3 ^ 2 / 2) -
      3 * ((min (w 5) (w 7) - max (w 4) (w 6))⁺ - w 1 * w 3 / 2) with hΦ
  have hΦc : Continuous Φ := by
    simp only [hΦ, posPart_def]
    fun_prop
  have heq : innerSplitError = fun t => Φ (fun i => f i t) := by
    funext x
    simp only [innerSplitError, hΦ, hf, sq, integral_ellDeviation_mul_ellDeviation,
      inter_self, volume_real_normUpperSet, volume_real_normUpperSet_inter,
      allocationRemainder_eq_half_fract, baseHalfFract_eq_fract, hL, hR, one_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_assoc, α]
    simp only [show ∀ a : ℝ, 2 * (a / 2) = a from fun a => by ring]
    ring
  have hα : 0 < α := by simp only [α]; exact_mod_cast innerRatio_pos
  have hfr : ∀ c : ℝ, 0 < c →
      PiecewiseContinuousOnRefinable (fun t => Int.fract (2 * (c * t))) u v := by
    intro c hc
    refine piecewiseContinuousOnRefinable_comp_mul (φ := fun y => Int.fract (2 * y)) hc
      ⟨1, fun y => ?_⟩ (fun m => ⟨fun y => 2 * y - m, by fun_prop, fun y h₁ h₂ => ?_⟩) u v
    · rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
    · rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, m, by ring⟩
  have hLr : ∀ c : ℝ, 0 < c → PiecewiseContinuousOnRefinable (fun t => L (c * t)) u v := by
    intro c hc
    refine piecewiseContinuousOnRefinable_comp_mul hc ⟨1, fun y => ?_⟩ (fun m => ?_) u v
    · have := Int.fract_nonneg y
      have := Int.fract_lt_one y
      simp only [hL]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    · obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' m
      · refine ⟨fun _ => 0, continuous_const, fun y h₁ h₂ => ?_⟩
        obtain ⟨-, h⟩ := fract_eq_sub_of_two_mul_mem_Ioo_even h₁ h₂
        simp only [hL, ite_eq_left h]
      · refine ⟨fun y => 1 - (y - j), by fun_prop, fun y h₁ h₂ => ?_⟩
        obtain ⟨he, h⟩ := fract_eq_sub_of_two_mul_mem_Ioo_odd h₁ h₂
        simp only [hL, ite_eq_right h.not_gt, he]
  have hRr : ∀ c : ℝ, 0 < c → PiecewiseContinuousOnRefinable (fun t => R (c * t)) u v := by
    intro c hc
    refine piecewiseContinuousOnRefinable_comp_mul hc ⟨1, fun y => ?_⟩ (fun m => ?_) u v
    · have := Int.fract_nonneg y
      have := Int.fract_lt_one y
      simp only [hR]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    · obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' m
      · refine ⟨fun y => y - j, by fun_prop, fun y h₁ h₂ => ?_⟩
        obtain ⟨he, h⟩ := fract_eq_sub_of_two_mul_mem_Ioo_even h₁ h₂
        simp only [hR, ite_eq_left h, he]
      · refine ⟨fun _ => 1 / 2, continuous_const, fun y h₁ h₂ => ?_⟩
        obtain ⟨-, h⟩ := fract_eq_sub_of_two_mul_mem_Ioo_odd h₁ h₂
        simp only [hR, ite_eq_right h.not_gt]
  rw [heq]
  refine (PiecewiseContinuousOnRefinable.comp hΦc fun i => ?_).piecewiseContinuousOn huv
  fin_cases i
  exacts [hfr _ (by exact_mod_cast zero_lt_one.trans one_lt_heightRatio), hfr 1 one_pos,
    hfr _ (by exact_mod_cast orderRatio_pos), hfr α hα, hLr 1 one_pos, hRr 1 one_pos,
    hLr α hα, hRr α hα]

end Zeta5Irr
