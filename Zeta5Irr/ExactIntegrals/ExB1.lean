/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExFracpart

/-!
# The integral of `Ψ_u(z)²` over `[0, 1/2]`

Let `u` be real with fractional part `f = u - ⌊u⌋`, and put `c = d₀(f)`, so `0 ≤ c ≤ 1/2`.
Away from `z = c`, the function `Ψ_u(z)` on `(0, 1/2)` equals `e(f) (𝟙_{z < c} - 2c)` with
`e(f) = ±1`, so its square is `(1 - 2c)²` on `(0, c)` and `4c²` on `(c, 1/2)`. Hence
`∫₀^{1/2} Ψ_u(z)² dz = c (1 - 2c)² + (1/2 - c) 4c² = c (1 - 2c)`.

## Main results

* `Zeta5Irr.integral_psi_sq`: `∫₀^{1/2} Ψ_u(z)² dz = d₀(f) (1 - 2 d₀(f))`.

## Implementation notes

The source's hypothesis `f = u - ⌊u⌋` is expressed by substituting `Int.fract u` for `f`,
which is `u - ⌊u⌋` by definition. The integrand is identified with a constant on each of the
open intervals `(0, c)` and `(c, 1/2)`; since single points are Lebesgue-null, this determines
the interval integrals on `[0, c]` and `[c, 1/2]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1 (fractional parts and the two `z`-integrals).
-/

@[expose] public section

namespace Zeta5Irr

open intervalIntegral Set

/-- **Lemma (the integral of `Ψ_u²`).** For real `u` with fractional part `f = u - ⌊u⌋`,
`∫₀^{1/2} Ψ_u(z)² dz = d₀(f) (1 - 2 d₀(f))`. -/
@[zeta5irr "lem_ex_B1"]
theorem integral_psi_sq (u : ℝ) :
    ∫ z in (0 : ℝ)..1 / 2, psi u z ^ 2 = d₀ (Int.fract u) * (1 - 2 * d₀ (Int.fract u)) := by
  set c := d₀ (Int.fract u) with hc
  have hc₀ : 0 ≤ c := d₀_fract_nonneg u
  have hc₁ : c ≤ 1 / 2 := d₀_le_half _
  have hsq : ∀ z, 0 < z → z < 1 / 2 → z ≠ c →
      psi u z ^ 2 = ((if z < c then 1 else 0) - 2 * c) ^ 2 := fun z h₀ h₁ h => by
    rw [psi_eq_esign_mul u z h₀ h₁ h, mul_pow, esign_sq, one_mul]
  have h₁ : EqOn (fun z => psi u z ^ 2) (fun _ => (1 - 2 * c) ^ 2) (Ioo 0 c) :=
    fun z hz => by
      simp only
      rw [hsq z hz.1 (hz.2.trans_le hc₁) hz.2.ne, ite_eq_left hz.2]
  have h₂ : EqOn (fun z => psi u z ^ 2) (fun _ => (2 * c) ^ 2) (Ioo c (1 / 2)) :=
    fun z hz => by
      simp only
      rw [hsq z (hc₀.trans_lt hz.1) hz.2 hz.1.ne', ite_eq_right hz.1.not_gt]
      ring
  have i₁ : IntervalIntegrable (fun z => psi u z ^ 2) MeasureTheory.volume 0 c :=
    (intervalIntegrable_const (c := (1 - 2 * c) ^ 2)).congr_uIoo
      (fun z hz => (h₁ (uIoo_of_le hc₀ ▸ hz)).symm)
  have i₂ : IntervalIntegrable (fun z => psi u z ^ 2) MeasureTheory.volume c (1 / 2) :=
    (intervalIntegrable_const (c := (2 * c) ^ 2)).congr_uIoo
      (fun z hz => (h₂ (uIoo_of_le hc₁ ▸ hz)).symm)
  rw [← integral_add_adjacent_intervals i₁ i₂, integral_congr_Ioo_of_le hc₀ h₁,
    integral_congr_Ioo_of_le hc₁ h₂, integral_const, integral_const, smul_eq_mul, smul_eq_mul]
  ring

end Zeta5Irr
