/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExFracpart

/-!
# The mixed integral `∫₀^{1/2} Ψ_u Ψ_v`

For real `u` and `v` with fractional parts `f = u - ⌊u⌋` and `g = v - ⌊v⌋`,
`∫₀^{1/2} Ψ_u(z) Ψ_v(z) dz = e(f) e(g) (min(d₀(f), d₀(g)) - 2 d₀(f) d₀(g))`.

Away from the two points `d₀(f)` and `d₀(g)`, the integrand equals
`e(f) e(g) (𝟙_{z < d₀(f)} - 2 d₀(f)) (𝟙_{z < d₀(g)} - 2 d₀(g))`, which expands into a linear
combination of indicators `𝟙_{z < w}` and a constant; each indicator with `0 ≤ w ≤ 1/2`
integrates to `w`.

## Main results

* `Zeta5Irr.integral_psi_mul_psi`: the value of `∫₀^{1/2} Ψ_u(z) Ψ_v(z) dz`.

## Implementation notes

The source's hypotheses `f = u - ⌊u⌋` and `g = v - ⌊v⌋` are expressed by substituting
`Int.fract u` and `Int.fract v`, which are these differences by definition. The indicator
`𝟙_{z < w}` is written `if z < w then 1 else 0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1 (fractional parts and the two `z`-integrals).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- **Lemma (the mixed `B₁` integral).** For real `u`, `v` with fractional parts
`f = u - ⌊u⌋` and `g = v - ⌊v⌋`,
`∫₀^{1/2} Ψ_u(z) Ψ_v(z) dz = e(f) e(g) (min(d₀(f), d₀(g)) - 2 d₀(f) d₀(g))`. -/
@[zeta5irr "lem_ex_B1_mixed"]
theorem integral_psi_mul_psi (u v : ℝ) :
    ∫ z in (0 : ℝ)..1 / 2, psi u z * psi v z =
      esign (Int.fract u) * esign (Int.fract v) *
        (min (d₀ (Int.fract u)) (d₀ (Int.fract v)) -
          2 * d₀ (Int.fract u) * d₀ (Int.fract v)) := by
  set c₁ := d₀ (Int.fract u)
  set c₂ := d₀ (Int.fract v)
  set e := esign (Int.fract u) * esign (Int.fract v)
  have hc₁ : 0 ≤ c₁ := d₀_fract_nonneg u
  have hc₂ : 0 ≤ c₂ := d₀_fract_nonneg v
  have hc₁' : c₁ ≤ 1 / 2 := d₀_le_half _
  have hc₂' : c₂ ≤ 1 / 2 := d₀_le_half _
  let I : ℝ → ℝ → ℝ := fun w z => if z < w then 1 else 0
  have hI (w a b : ℝ) : IntervalIntegrable (I w) volume a b := intervalIntegrable_ite_lt w a b
  have key : ∫ z in (0 : ℝ)..1 / 2, psi u z * psi v z =
      ∫ z in (0 : ℝ)..1 / 2, (e * I (min c₁ c₂) z - (2 * c₂ * e) * I c₁ z -
        (2 * c₁ * e) * I c₂ z + 4 * c₁ * c₂ * e) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume c₁, Measure.ae_ne volume c₂,
      Measure.ae_ne volume (1 / 2)] with z h1 h2 h3 hz
    rw [uIoc_of_le (by norm_num)] at hz
    have hz' : z < 1 / 2 := lt_of_le_of_ne hz.2 h3
    rw [psi_eq_esign_mul u z hz.1 hz' h1, psi_eq_esign_mul v z hz.1 hz' h2]
    simp only [I, e, c₁, c₂, lt_min_iff]
    split_ifs <;> first | (exfalso; tauto) | ring
  rw [key, intervalIntegral.integral_add
      ((((hI _ _ _).const_mul _).sub ((hI _ _ _).const_mul _)).sub ((hI _ _ _).const_mul _))
      intervalIntegrable_const,
    intervalIntegral.integral_sub (((hI _ _ _).const_mul _).sub ((hI _ _ _).const_mul _))
      ((hI _ _ _).const_mul _),
    intervalIntegral.integral_sub ((hI _ _ _).const_mul _) ((hI _ _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [I]
  rw [integral_ite_lt (le_min hc₁ hc₂) (min_le_left _ _ |>.trans hc₁'), integral_ite_lt hc₁ hc₁',
    integral_ite_lt hc₂ hc₂']
  simp only [smul_eq_mul]
  ring

end Zeta5Irr
