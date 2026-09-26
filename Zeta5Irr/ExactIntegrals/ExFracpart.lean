/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.D0
public import Zeta5Irr.ExactIntegrals.Esign
public import Zeta5Irr.ExactIntegrals.ExPsi

/-!
# `Ψ_u(z)` in terms of the fractional part of `u`

Let `f = u - ⌊u⌋` be the fractional part of `u` and `0 < z < 1/2` with `z ≠ d₀(f)`. Then
`Ψ_u(z) = ℓ(u, z) - 2u` is piecewise constant in `z`:
`Ψ_u(z) = e(f) (𝟙_{z < d₀(f)} - 2 d₀(f))`,
where `d₀(f) = min(f, 1 - f)` and `e(f)` is `1` for `f ≤ 1/2` and `-1` otherwise.

## Main results

* `Zeta5Irr.psi_eq_esign_mul_of_mem_Ico`: the formula for `u` itself in `[0, 1)`.
* `Zeta5Irr.psi_eq_esign_mul`: the formula for arbitrary real `u`, with `f = Int.fract u`.
* `Zeta5Irr.intervalIntegrable_ite_lt`, `Zeta5Irr.integral_ite_lt`: the step function
  `𝟙_{z < w}` is interval integrable, with `∫₀^b 𝟙_{z < w} dz = w` for `0 ≤ w ≤ b`.

## Implementation notes

The source's hypothesis `f = u - ⌊u⌋` is expressed by substituting `Int.fract u` for `f`,
which is `u - ⌊u⌋` by definition. The indicator `𝟙_{z < d₀(f)}` is written as
`if z < d₀ f then 1 else 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1 (fractional parts and the two `z`-integrals).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `0 ≤ f < 1`, `0 < z < 1/2` and `z ≠ d₀(f)`,
`Ψ_f(z) = e(f) (𝟙_{z < d₀(f)} - 2 d₀(f))`. -/
theorem psi_eq_esign_mul_of_mem_Ico {f z : ℝ} (hf₀ : 0 ≤ f) (hf₁ : f < 1) (hz₀ : 0 < z)
    (hz₁ : z < 1 / 2) (hz : z ≠ d₀ f) :
    psi f z = esign f * ((if z < d₀ f then 1 else 0) - 2 * d₀ f) := by
  rw [psi_def, ell_def]
  push_cast
  rcases le_or_gt f (1 / 2) with hf | hf
  · have hd : d₀ f = f := min_eq_left (by linarith)
    rw [esign_of_le hf]; rw [hd] at hz ⊢
    have h₂ : ⌊f + z⌋ = 0 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rcases lt_or_gt_of_ne hz with h | h
    · have h₁ : ⌊f - z⌋ = 0 :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp [h₁, h₂, h]
    · have h₁ : ⌊f - z⌋ = -1 :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp [h₁, h₂, h.not_gt]
  · have hd : d₀ f = 1 - f := min_eq_right (by linarith)
    rw [esign_of_lt hf]; rw [hd] at hz ⊢
    have h₁ : ⌊f - z⌋ = 0 := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rcases lt_or_gt_of_ne hz with h | h
    · have h₂ : ⌊f + z⌋ = 0 :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp [h₁, h₂, h]
      ring
    · have h₂ : ⌊f + z⌋ = 1 :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp [h₁, h₂, h.not_gt]
      ring

/-- **Lemma (`Ψ_u` via the fractional part).** For real `u` with fractional part
`f = u - ⌊u⌋`, and `0 < z < 1/2` with `z ≠ d₀(f)`,
`Ψ_u(z) = e(f) (𝟙_{z < d₀(f)} - 2 d₀(f))`. -/
@[zeta5irr "lem_ex_fracpart"]
theorem psi_eq_esign_mul (u z : ℝ) (hz₀ : 0 < z) (hz₁ : z < 1 / 2)
    (hz : z ≠ d₀ (Int.fract u)) :
    psi u z = esign (Int.fract u) *
      ((if z < d₀ (Int.fract u) then 1 else 0) - 2 * d₀ (Int.fract u)) := by
  conv_lhs => rw [← Int.fract_add_floor u, psi_add_intCast]
  exact psi_eq_esign_mul_of_mem_Ico (Int.fract_nonneg u) (Int.fract_lt_one u) hz₀ hz₁ hz

section StepIntegral

open MeasureTheory Set

/-- The indicator `z ↦ 𝟙_{z < w}` is interval integrable on every interval. -/
theorem intervalIntegrable_ite_lt (w a b : ℝ) :
    IntervalIntegrable (fun z : ℝ => if z < w then (1 : ℝ) else 0) volume a b := by
  refine Antitone.intervalIntegrable fun x y hxy => ?_
  split_ifs <;> first | (exfalso; linarith) | norm_num

/-- For `0 ≤ w ≤ b`, `∫₀^b 𝟙_{z < w} dz = w`. -/
theorem integral_ite_lt {w b : ℝ} (hw₀ : 0 ≤ w) (hwb : w ≤ b) :
    ∫ z in (0 : ℝ)..b, (if z < w then (1 : ℝ) else 0) = w := by
  have h : (fun z : ℝ => if z < w then (1 : ℝ) else 0) = (Iio w).indicator 1 := by
    ext z; simp [indicator_apply]
  rw [h, intervalIntegral.integral_of_le (hw₀.trans hwb), integral_indicator_one measurableSet_Iio]
  have : Iio w ∩ Ioc 0 b = Ioo 0 w := by
    ext z; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]; constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  simp [Measure.real, Measure.restrict_apply measurableSet_Iio, this, hw₀]

end StepIntegral

end Zeta5Irr
