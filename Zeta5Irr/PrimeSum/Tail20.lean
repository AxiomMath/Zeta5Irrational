/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.TailIbp

/-!
# The tail integral from `20`

We show `∫_{20}^∞ R(x) / x³ dx ≤ -2689/48000`, where `R` is the inner limiting function.

The integration-by-parts formula for the tail integral is applied with `x₀ = 20`. Since
`{20} = 0` and `{α · 20} = {3/2} = 1/2`, the first periodic antiderivative takes the value
`𝒫(20) = 37/2` and the second vanishes, `𝒫₂(20) = 0`. The remaining two integrals are bounded
using `|𝒫₂| ≤ 16` and `𝓔 ≤ 13/8` together with `∫_{20}^∞ x⁻⁴ dx = 1/24000` and
`∫_{20}^∞ x⁻³ dx = 1/800`. Collecting terms over the denominator `96000` gives
`(-4440 - 4440 + 2923 + 384 + 195) / 96000 = -2689/48000`.

## Main results

* `Zeta5Irr.integral_Ioi_twenty_innerLimitingR_div_pow_three_le`: the bound
  `∫_{20}^∞ R(x) / x³ dx ≤ -2689/48000`.

## Implementation notes

The estimate `∫_c^∞ g(x) / x^k dx ≤ C / ((k - 1) c^(k-1))` for `g ≤ C`, `C ≥ 0`, is proved
without an integrability hypothesis on `g`: if the integrand is not integrable, its Bochner
integral is `0`, which is below the nonnegative bound.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set

/-- **The tail integral from `20`.** `∫_{20}^∞ R(x) / x³ dx ≤ -2689/48000`. -/
@[zeta5irr "lem_tail_20"]
theorem integral_Ioi_twenty_innerLimitingR_div_pow_three_le :
    ∫ x in Ioi (20 : ℝ), innerLimitingR x / x ^ 3 ≤ -2689 / 48000 := by
  rw [integral_Ioi_innerLimitingR_div_pow_three_eq (by norm_num)]
  have hα : (innerRatio : ℝ) * 20 = 1 + 1 / 2 := by norm_num [innerRatio]
  have hfα : Int.fract ((innerRatio : ℝ) * 20) = 1 / 2 := by
    rw [hα, add_comm, ← Nat.cast_one (R := ℝ), Int.fract_add_natCast]
    norm_num
  have hf : Int.fract (20 : ℝ) = 0 := by
    exact_mod_cast Int.fract_natCast (R := ℝ) 20
  have hP : firstPeriodicAntideriv 20 = 37 / 2 := by
    rw [firstPeriodicAntideriv, hfα, hf]; norm_num
  have hP₂ : secondPeriodicAntideriv 20 = 0 := by
    rw [secondPeriodicAntideriv, hfα, hf]; norm_num [cubicKernel]
  have h4 := setIntegral_Ioi_div_pow_le (g := secondPeriodicAntideriv) (c := 20)
    (C := 16) (k := 4) (by norm_num) (by norm_num) (by norm_num)
    (fun x _ => (abs_le.1 (abs_secondPeriodicAntideriv_le x)).2)
  have h3 := setIntegral_Ioi_div_pow_le (g := innerSplitError) (c := 20)
    (C := 13 / 8) (k := 3) (by norm_num) (by norm_num) (by norm_num)
    (fun x _ => innerSplitError_le x)
  rw [hP, hP₂]
  norm_num [orderRatio] at h4 h3 ⊢
  linarith

end Zeta5Irr
