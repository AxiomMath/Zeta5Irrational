/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.MKMBound
public import Zeta5Irr.PrimeSum.Tail20
public import Zeta5Irr.PrimeSum.TailM
public import Zeta5Irr.ExactIntegrals.AM
public import Zeta5Irr.ExactIntegrals.InnerIntegral
public import Zeta5Irr.ExactIntegrals.IoutValue

/-!
# The tail integral and the final bound on the normalizing factor

Let `M ≥ 40` be an integer divisible by `40`. Splitting
`∫_3^M R(x) x⁻³ dx = ∫_3^{20} + ∫_{20}^∞ - ∫_M^∞` and inserting the exact value of the first
integral and the bounds on the two tails gives
```
∫_3^M R(x) / x³ dx ≤ 322437603634266857629 / 7535670527041937280000 - 2689 / 48000
  + λ / M - (2923/240 - 1/4) / M² + 32 / M³.
```
Together with the growth of the normalizing factor, `limsup log m_{K,M} / K² ≤ I_out + 6 λ / M +
∫_3^M R(x) x⁻³ dx`, and `I_out = 127751/96000`, the three rational constants sum to `A_*`, so
```
limsup_{K → ∞, 40 ∣ K} log m_{K,M} / K² ≤ A_M.
```

## Main results

* `Zeta5Irr.integral_innerLimitingR_div_pow_three_le_of_forty_dvd`: the bound on
  `∫_3^M R(x) x⁻³ dx`.
* `Zeta5Irr.limsup_log_normalizingFactor_div_sq_le_AM`: `limsup log m_{K,M} / K² ≤ A_M`.

## Implementation notes

Since `K = 40 n`, the `limsup` over `K ∈ 40 ℤ` is the `limsup` as `n → ∞`, with `K` written
`Zeta5Irr.poleBound n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open Filter MeasureTheory Set

variable {M : ℕ}

/-- For an integer `M ≥ 40` divisible by `40`,
`∫_3^M R(x) / x³ dx ≤ 322437603634266857629 / 7535670527041937280000 - 2689 / 48000
+ λ / M - (2923/240 - 1/4) / M² + 32 / M³`. -/
theorem integral_innerLimitingR_div_pow_three_le_of_forty_dvd (hM : 40 ∣ M) (hM40 : 40 ≤ M) :
    ∫ x in (3 : ℝ)..M, innerLimitingR x / x ^ 3 ≤
      322437603634266857629 / 7535670527041937280000 - 2689 / 48000 +
        (orderRatio : ℝ) / M - (2923 / 240 - 1 / 4) / (M : ℝ) ^ 2 + 32 / (M : ℝ) ^ 3 := by
  have hint : ∀ {x₀ : ℝ}, 0 < x₀ →
      IntegrableOn (fun x => innerLimitingR x / x ^ 3) (Ioi x₀) := fun hx₀ =>
    (integrableOn_innerLimitingR_div_pow_three_Ici hx₀).mono_set Ioi_subset_Ici_self
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h3M := intervalIntegral.integral_Ioi_sub_Ioi' (hint (by norm_num : (0 : ℝ) < 3))
    (hint hM0)
  have h320 := intervalIntegral.integral_Ioi_sub_Ioi' (hint (by norm_num : (0 : ℝ) < 3))
    (hint (by norm_num : (0 : ℝ) < 20))
  have hMint : (40 : ℤ) ∣ (M : ℤ) := by exact_mod_cast hM
  have htailM := integral_Ioi_innerLimitingR_div_pow_three_ge_of_forty_dvd hMint
    (by exact_mod_cast hM40)
  push_cast at htailM
  have h20 := integral_Ioi_twenty_innerLimitingR_div_pow_three_le
  rw [integral_innerLimitingR_div_pow_three] at h320
  rw [← h3M]
  linarith

/-- **The final bound on the normalizing factor.** For every integer `M ≥ 40` divisible by `40`,
`limsup_{K → ∞, 40 ∣ K} log m_{K,M} / K² ≤ A_M`. -/
@[zeta5irr "prop_mKM_final"]
theorem limsup_log_normalizingFactor_div_sq_le_AM (hM : 40 ∣ M) (hM40 : 40 ≤ M) :
    limsup (fun n : ℕ => Real.log (normalizingFactor n M) / (poleBound n : ℝ) ^ 2) atTop ≤
      AM M := by
  refine (limsup_log_normalizingFactor_div_sq_le hM40).trans ?_
  have h := integral_innerLimitingR_div_pow_three_le_of_forty_dvd hM hM40
  rw [outerIntegral_value, AM, Astar]
  push_cast
  have : (orderRatio : ℝ) / M * 6 = 6 * (orderRatio : ℝ) / M := by ring
  have : (orderRatio : ℝ) / M * 7 = 7 * (orderRatio : ℝ) / M := by ring
  linarith

end Zeta5Irr
