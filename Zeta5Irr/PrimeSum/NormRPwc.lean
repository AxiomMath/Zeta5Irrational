/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.QRSplit
public import Zeta5Irr.PrimeSum.NormEcalPwc

/-!
# Piecewise continuity of the inner limiting function `R`

For all reals `u < v`, the inner limiting function `R` is piecewise continuous on `[u, v]`.

By the splitting `R(x) = x Φ(x) + 𝓔(x)` with `Φ(x) = 4λ + 2λ{x} - 12λ{αx}`, the function `R`
is a continuous (polynomial) function of the four functions `x`, `{x}`, `{αx}` and `𝓔(x)`.
The first is continuous; each fractional part `{cx}` (`c > 0`) is bounded and affine between
consecutive points of a discrete set; and `𝓔` is piecewise continuous. Taking a common
refinement of the partitions gives piecewise continuity of `R`.

## Main results

* `Zeta5Irr.PiecewiseContinuousOnRefinable.of_continuousOn`: a function continuous on `[u, v]`
  is refinably piecewise continuous there.
* `Zeta5Irr.PiecewiseContinuousOn.piecewiseContinuousOnRefinable`: a piecewise continuous
  function is refinably piecewise continuous, the exceptional set being its partition.
* `Zeta5Irr.piecewiseContinuousOnRefinable_fract_mul`: `t ↦ {c t}` (`c > 0`) is refinably
  piecewise continuous on every `[u, v]`.
* `Zeta5Irr.piecewiseContinuousOn_innerLimitingR`: `R` is piecewise continuous on `[u, v]`.

## Implementation notes

* The source states the result for `3 ≤ u < v`. The splitting `R(x) = x Φ(x) + 𝓔(x)` and the
  piecewise continuity of `𝓔` hold for all `x` and all `u < v` respectively, so the lemma is
  stated for all `u < v`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.6 (Piecewise continuity).
-/

@[expose] public section

namespace Zeta5Irr

open Set

namespace PiecewiseContinuousOnRefinable

/-- A function continuous on `[u, v]` is refinably piecewise continuous there, with empty
exceptional set. -/
theorem of_continuousOn {f : ℝ → ℝ} {u v : ℝ} (hf : ContinuousOn f (Icc u v)) :
    PiecewiseContinuousOnRefinable f u v := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hf).isBounded.exists_norm_le
  refine ⟨⟨C, fun t ht => hC _ ⟨t, ht, rfl⟩⟩, ∅, finite_empty,
    fun a b hua _ hbv _ => ⟨f, hf.mono (Icc_subset_Icc hua hbv), eqOn_refl _ _⟩⟩

end PiecewiseContinuousOnRefinable

/-- A piecewise continuous function on `[u, v]` is refinably piecewise continuous there, the
exceptional set being the points of its partition. -/
theorem PiecewiseContinuousOn.piecewiseContinuousOnRefinable {f : ℝ → ℝ} {u v : ℝ}
    (hf : PiecewiseContinuousOn f u v) : PiecewiseContinuousOnRefinable f u v := by
  classical
  obtain ⟨r, p, hr, hp, h0, hlast, hb, h⟩ := hf
  refine ⟨hb, range p, finite_range p, fun a b hua hab hbv hD => ?_⟩
  set S : Finset (Fin (r + 1)) := Finset.univ.filter (fun i => p i ≤ a) with hS
  have hSne : S.Nonempty := ⟨0, by simp [S, h0, hua]⟩
  set i := S.max' hSne
  have hi : p i ≤ a := (Finset.mem_filter.1 (S.max'_mem hSne)).2
  have hmax : ∀ j, p j ≤ a → j ≤ i := fun j hj => S.le_max' j (by simp [S, hj])
  have hil : i ≠ Fin.last r := by
    rintro hi'
    rw [hi', hlast] at hi
    linarith
  obtain ⟨k, hk⟩ : ∃ k : Fin r, k.castSucc = i := Fin.exists_castSucc_eq.2 hil
  have ha : a < p k.succ := by
    by_contra hcon
    have := hmax _ (not_lt.1 hcon)
    rw [← hk, Fin.le_def] at this
    simp at this
  have hb' : b ≤ p k.succ := by
    by_contra hcon
    exact Set.disjoint_left.1 hD ⟨ha, not_le.1 hcon⟩ ⟨k.succ, rfl⟩
  obtain ⟨g, hg, hfg⟩ := h k
  rw [hk] at hg hfg
  exact ⟨g, hg.mono (Icc_subset_Icc hi hb'), hfg.mono (Ioo_subset_Ioo hi hb')⟩

/-- For `c > 0`, the function `t ↦ {c t}` is refinably piecewise continuous on every
`[u, v]`. -/
theorem piecewiseContinuousOnRefinable_fract_mul {c : ℝ} (hc : 0 < c) (u v : ℝ) :
    PiecewiseContinuousOnRefinable (fun t => Int.fract (c * t)) u v := by
  refine piecewiseContinuousOnRefinable_comp_mul hc ⟨1, fun y => ?_⟩ (fun m => ?_) u v
  · rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
  · obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' m
    · exact ⟨fun y => y - j, by fun_prop,
        fun y h₁ h₂ => (fract_eq_sub_of_two_mul_mem_Ioo_even h₁ h₂).1⟩
    · exact ⟨fun y => y - j, by fun_prop,
        fun y h₁ h₂ => (fract_eq_sub_of_two_mul_mem_Ioo_odd h₁ h₂).1⟩

/-- **Piecewise continuity of `R`.** For all reals `u < v` (the source takes `3 ≤ u`), the
inner limiting function `R` is piecewise continuous on `[u, v]`. -/
@[zeta5irr "lem_norm_R_pwc"]
theorem piecewiseContinuousOn_innerLimitingR {u v : ℝ} (huv : u < v) :
    PiecewiseContinuousOn innerLimitingR u v := by
  set f : Fin 4 → ℝ → ℝ := ![fun t => t, fun t => Int.fract (1 * t),
    fun t => Int.fract ((innerRatio : ℝ) * t), innerSplitError] with hf
  set Ψ : (Fin 4 → ℝ) → ℝ := fun w =>
    w 0 * (4 * (orderRatio : ℝ) + 2 * orderRatio * w 1 - 12 * orderRatio * w 2) + w 3 with hΨ
  have hΨc : Continuous Ψ := by simp only [hΨ]; fun_prop
  have heq : innerLimitingR = fun t => Ψ (fun i => f i t) := by
    funext x
    simp [innerLimitingR_eq, hΨ, hf, sawtoothSlope]
  rw [heq]
  refine (PiecewiseContinuousOnRefinable.comp hΨc fun i => ?_).piecewiseContinuousOn huv
  fin_cases i
  exacts [.of_continuousOn continuousOn_id, piecewiseContinuousOnRefinable_fract_mul one_pos u v,
    piecewiseContinuousOnRefinable_fract_mul (by exact_mod_cast innerRatio_pos) u v,
    (piecewiseContinuousOn_innerSplitError huv).piecewiseContinuousOnRefinable]

end Zeta5Irr
