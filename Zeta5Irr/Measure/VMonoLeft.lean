/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Measure.VZero
public import Zeta5Irr.Measure.VDerivSpec
public import Zeta5Irr.Measure.VIncreasingLow
public import Zeta5Irr.Measure.VMinLocate

/-!
# The external field is nonincreasing on `[0, q₋]`

Let `V` be the external field and `W` its derivative in the square-root variable, and let
`q₋ = 59205077 / 10¹⁰`. Then `V(t) ≤ V(s)` whenever `0 ≤ s ≤ t ≤ q₋`.

Since `√q₋ < 4/5` and `W` is strictly increasing on `(0, 4/5)`, we get `W(y) ≤ W(√q₋) < 0` for
`0 < y ≤ √q₋`. As `y ↦ V(y²)` has derivative `W`, it is nonincreasing on `(0, √q₋]`, which gives
the claim for `0 < s`. For `s = 0`, the closed formula for `V` on `(0, ∞)` shows that `V` is
continuous from the right at `0`, and one passes to the limit.

## Main results

* `Zeta5Irr.fieldDeriv_neg_of_le_sqrt`: `W(y) < 0` for `0 < y ≤ √q₋`.
* `Zeta5Irr.tendsto_externalField_zero`: `V(x) → V(0)` as `x → 0⁺`.
* `Zeta5Irr.antitoneOn_externalField`: `V` is antitone on `[0, q₋]`.
* `Zeta5Irr.externalField_le_of_le`: `V(t) ≤ V(s)` for `0 ≤ s ≤ t ≤ q₋`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §9.5 (The shape of the field).
-/

@[expose] public section

namespace Zeta5Irr

open Real Set Filter Topology

/-- `W(y) < 0` for `0 < y ≤ √q₋`. -/
theorem fieldDeriv_neg_of_le_sqrt {y : ℝ} (hy : 0 < y)
    (hyq : y ≤ √(externalFieldMinLower : ℝ)) : fieldDeriv y < 0 := by
  have hq : √(externalFieldMinLower : ℝ) < 4 / 5 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num [externalFieldMinLower]
  rcases hyq.lt_or_eq with h | h
  · exact (strictMonoOn_fieldDeriv_Ioo ⟨hy, h.trans hq⟩ ⟨hy.trans h, hq⟩ h).trans
      fieldDeriv_sqrt_externalFieldMinLower_neg
  · exact h ▸ fieldDeriv_sqrt_externalFieldMinLower_neg

/-- The external field is continuous from the right at `0`: `V(x) → V(0)` as `x → 0⁺`. -/
theorem tendsto_externalField_zero :
    Tendsto externalField (𝓝[>] 0) (𝓝 (externalField 0)) := by
  set a : ℝ := (innerRatio : ℝ)
  have ha : 0 < a := by simp [a, innerRatio]
  let g : ℝ → ℝ := fun t => log (1 + t) - 6 * a * log (t + a ^ 2) - 2 + 12 * a
  let h : ℝ → ℝ := fun t => 2 * √t * (π + arctan (1 / √t) - 6 * arctan (a / √t))
  have hV : externalField =ᶠ[𝓝[>] 0] fun t => g t + h t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact externalField_eq ht
  refine Tendsto.congr' hV.symm ?_
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
    have : ContinuousAt g 0 := by
      have : a ^ 2 ≠ 0 := by positivity
      simp only [g]
      fun_prop (disch := simp [*])
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto h (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * √t) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => 2 * √t) (𝓝 0) (𝓝 (2 * √0)) :=
        (continuous_const.mul continuous_sqrt).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine h1.zero_mul_isBoundedUnder_le ?_
    refine isBoundedUnder_of ⟨9 / 2 * π, fun t => ?_⟩
    simp only [Function.comp_apply, norm_eq_abs]
    have := arctan_lt_pi_div_two (1 / √t)
    have := neg_pi_div_two_lt_arctan (1 / √t)
    have := arctan_lt_pi_div_two (a / √t)
    have := neg_pi_div_two_lt_arctan (a / √t)
    have := pi_pos
    rw [abs_le]
    constructor <;> linarith
  have key : g 0 + 0 = externalField 0 := by
    rw [externalField_zero]
    simp only [g, a, add_zero, zero_add, log_one, log_pow]
    push_cast
    ring
  simpa [key] using hg.add hh

/-- **`V` is nonincreasing on `[0, q₋]`.** -/
@[zeta5irr "lem_V_mono_left"]
theorem antitoneOn_externalField :
    AntitoneOn externalField (Icc 0 (externalFieldMinLower : ℝ)) := by
  set q : ℝ := (externalFieldMinLower : ℝ)
  have hf : AntitoneOn (fun y : ℝ => externalField (y ^ 2)) (Ioc 0 √q) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fieldDeriv) (convex_Ioc _ _) ?_ ?_ ?_
    · exact fun y hy => (hasDerivAt_externalField_sq hy.1).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      exact (hasDerivAt_externalField_sq hy.1).hasDerivWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      exact (fieldDeriv_neg_of_le_sqrt hy.1 hy.2.le).le
  have hpos : ∀ ⦃s t : ℝ⦄, 0 < s → s ≤ t → t ≤ q → externalField t ≤ externalField s := by
    intro s t hs hst htq
    simpa only [sq_sqrt hs.le, sq_sqrt (hs.le.trans hst)] using
      hf ⟨sqrt_pos.2 hs, sqrt_le_sqrt (hst.trans htq)⟩
        ⟨sqrt_pos.2 (hs.trans_le hst), sqrt_le_sqrt htq⟩ (sqrt_le_sqrt hst)
  intro s ⟨hs, _⟩ t ⟨_, htq⟩ hst
  rcases hs.lt_or_eq with hs | rfl
  · exact hpos hs hst htq
  rcases hst.lt_or_eq with ht | rfl
  · refine ge_of_tendsto tendsto_externalField_zero ?_
    filter_upwards [Ioc_mem_nhdsGT ht] with x hx
    exact hpos hx.1 hx.2 htq
  · exact le_rfl

/-- For `0 ≤ s ≤ t ≤ q₋`, `V(t) ≤ V(s)`. -/
theorem externalField_le_of_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ (externalFieldMinLower : ℝ)) : externalField t ≤ externalField s :=
  antitoneOn_externalField ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hst

end Zeta5Irr
