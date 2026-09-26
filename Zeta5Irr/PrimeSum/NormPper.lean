/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic

/-!
# The first periodic antiderivative `𝒫`

For `x ∈ ℝ` the first periodic antiderivative is
`𝒫(x) = 74 {α x} (1 - {α x}) - λ {x} (1 - {x})`, where `{·}` is the fractional part and
`α = 3/40`, `λ = 37/40` are the ratios of the construction. Each summand is the continuous
periodic function `t ↦ {t} (1 - {t})` composed with a dilation, so `𝒫` is continuous, and
since `40 α = 3` is an integer, `𝒫` is periodic of period `40`. It arises when the tail of the
prime sum is integrated by parts.

## Main definitions

* `Zeta5Irr.firstPeriodicAntideriv`: the function
  `x ↦ 74 {α x} (1 - {α x}) - λ {x} (1 - {x})` on `ℝ`.

## Main results

* `Zeta5Irr.firstPeriodicAntideriv_zero`: `𝒫(0) = 0`.
* `Zeta5Irr.periodic_firstPeriodicAntideriv`: `𝒫` is periodic of period `40`.
* `Zeta5Irr.continuous_firstPeriodicAntideriv`: `𝒫` is continuous.
* `Zeta5Irr.hasDerivAt_fract`: `{·}` has derivative `1` at every non-integer.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9: the tail integral.
-/

@[expose] public section

namespace Zeta5Irr

/-- The first periodic antiderivative `𝒫(x) = 74 {α x} (1 - {α x}) - λ {x} (1 - {x})`, with
`α = 3/40` the inner ratio, `λ = 37/40` the order ratio and `{·}` the fractional part. -/
@[zeta5irr "def_norm_Pper"]
noncomputable def firstPeriodicAntideriv (x : ℝ) : ℝ :=
  74 * Int.fract ((innerRatio : ℝ) * x) * (1 - Int.fract ((innerRatio : ℝ) * x)) -
    (orderRatio : ℝ) * Int.fract x * (1 - Int.fract x)

/-- `𝒫(0) = 0`. -/
@[simp]
theorem firstPeriodicAntideriv_zero : firstPeriodicAntideriv 0 = 0 := by
  simp [firstPeriodicAntideriv]

/-- `𝒫` is periodic of period `40`, since `40` and `40 α = 3` are both integers. -/
theorem firstPeriodicAntideriv_add_forty (x : ℝ) :
    firstPeriodicAntideriv (x + 40) = firstPeriodicAntideriv x := by
  have h : (innerRatio : ℝ) * (x + 40) = (innerRatio : ℝ) * x + (3 : ℤ) := by
    simp only [innerRatio]; push_cast; ring
  have h40 : x + 40 = x + (40 : ℤ) := by push_cast; ring
  rw [firstPeriodicAntideriv, firstPeriodicAntideriv, h, Int.fract_add_intCast, h40,
    Int.fract_add_intCast]

/-- `𝒫` is periodic of period `40`. -/
theorem periodic_firstPeriodicAntideriv : Function.Periodic firstPeriodicAntideriv 40 :=
  firstPeriodicAntideriv_add_forty

/-- The function `t ↦ {t} (1 - {t})` is continuous on `ℝ`. -/
theorem continuous_fract_mul_one_sub_fract :
    Continuous fun t : ℝ => Int.fract t * (1 - Int.fract t) :=
  (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn.comp_fract''
    (f := fun t : ℝ => t * (1 - t)) (by simp)

/-- `𝒫` is continuous. -/
@[zeta5irr "lem_norm_P_cont"]
theorem continuous_firstPeriodicAntideriv : Continuous firstPeriodicAntideriv := by
  have h := continuous_fract_mul_one_sub_fract
  have h1 := h.comp (continuous_const_mul ((innerRatio : ℝ)))
  unfold firstPeriodicAntideriv
  simp only [mul_assoc]
  exact (continuous_const.mul h1).sub (continuous_const.mul h)

section Fract

open Filter Topology

/-- Near a non-integer `t`, the fractional part agrees with `s ↦ s - ⌊t⌋`. -/
theorem fract_eventuallyEq_sub_floor {t : ℝ} (ht : t ∉ Set.range ((↑) : ℤ → ℝ)) :
    Int.fract =ᶠ[𝓝 t] fun s => s - ⌊t⌋ := by
  have hlt : (⌊t⌋ : ℝ) < t :=
    lt_of_le_of_ne (Int.floor_le t) fun h => ht ⟨⌊t⌋, h⟩
  have hmem : Set.Ioo (⌊t⌋ : ℝ) (⌊t⌋ + 1) ∈ 𝓝 t :=
    Ioo_mem_nhds hlt (Int.lt_floor_add_one t)
  filter_upwards [hmem] with s hs
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨hs.1.le, hs.2⟩]

/-- The fractional part has derivative `1` at every non-integer. -/
theorem hasDerivAt_fract {t : ℝ} (ht : t ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt Int.fract 1 t :=
  ((hasDerivAt_id t).sub_const _).congr_of_eventuallyEq (fract_eventuallyEq_sub_floor ht)

end Fract

end Zeta5Irr
