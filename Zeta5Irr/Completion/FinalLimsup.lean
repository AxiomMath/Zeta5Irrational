/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.MKMFinal
public import Zeta5Irr.RealDeterminant.Real
public import Zeta5Irr.ExactIntegrals.U
public import Zeta5Irr.PrimeSum.QKM

/-!
# The combined `K²`-scale bound

Let `ξ = ζ(5)`, let `M ≥ 40` be an integer divisible by `40`, and let `K = 40 n`. Since
`Q_{K,M}(ξ) = m_{K,M} F_K(ξ)` with both factors positive,
`K⁻² log Q_{K,M}(ξ) = K⁻² log m_{K,M} + K⁻² log F_K(ξ)`. The first term has `limsup` at most
`A_M`, and the second is at most `U + 24 (log K) / K + 200 / K`, whose lower-order part tends to
`0`. Hence
```
limsup_{K → ∞, 40 ∣ K} K⁻² log Q_{K,M}(ξ) ≤ A_M + U.
```

## Main results

* `Zeta5Irr.eventually_log_eval_normalizedPoly_div_sq_lt`: for every `b > A_M + U`, eventually
  `K⁻² log Q_{K,M}(ξ) < b`.
* `Zeta5Irr.limsup_log_eval_normalizedPoly_div_sq_le`: the `limsup` bound, in `EReal`.

## Implementation notes

* As elsewhere, `K = 40 n` and the `limsup` over `K ∈ 40 ℤ_{>0}` is the `limsup` as `n → ∞`.
  The side condition `K ≥ 200 M²` holds for all large `n`, so it does not affect the `limsup`
  and is not imposed.
* The sequence `K⁻² log Q_{K,M}(ξ)` is not known to be bounded below, and for a real sequence
  that is not the `limsup` of `Filter.limsup` is a junk value. The `limsup` is therefore taken
  in `EReal`, where it always has its intended meaning; the statement is equivalent to the
  eventual bound, which is the form used later.
* The bound on `limsup K⁻² log m_{K,M}` is available for `M` divisible by `40`, and this
  hypothesis is carried here; it holds for `M = 200`, where the result is applied.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

open Filter Topology Polynomial

namespace Zeta5Irr

variable {M : ℕ}

/-- `24 log K / K + 200 / K → 0` as `K = 40 n → ∞`. -/
theorem tendsto_mul_log_div_add_div_poleBound :
    Tendsto (fun n : ℕ => 24 * (Real.log (poleBound n) / poleBound n) + 200 / (poleBound n : ℝ))
      atTop (𝓝 0) := by
  have hK : Tendsto (fun n : ℕ => (poleBound n : ℝ)) atTop atTop := by
    simp only [poleBound, Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun x : ℝ => 200 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  simpa using ((h1.comp hK).const_mul 24).add (h2.comp hK)

/-- **The combined `K²`-scale bound, eventual form.** For an integer `M ≥ 40` divisible by `40`
and every real `b > A_M + U`, eventually `K⁻² log Q_{K,M}(ξ) < b` as `K = 40 n → ∞`. -/
@[zeta5irr "lem_final_limsup"]
theorem eventually_log_eval_normalizedPoly_div_sq_lt (hM : 40 ∣ M) (hM40 : 40 ≤ M) {b : ℝ}
    (hb : AM M + energyMargin < b) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((normalizedPoly n M).eval zetaFive) / (poleBound n : ℝ) ^ 2 < b := by
  set ε := b - (AM M + energyMargin) with hε
  have hε0 : 0 < ε := by linarith
  have ht := tendsto_log_normalizingFactor_div_sq hM40
  have hl := limsup_log_normalizingFactor_div_sq_le_AM hM hM40
  rw [ht.limsup_eq] at hl
  have h1 := ht.eventually (gt_mem_nhds (show _ < AM M + ε / 2 by linarith))
  have h2 := tendsto_mul_log_div_add_div_poleBound.eventually (gt_mem_nhds (half_pos hε0))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n h1 h2 hn
  have hK : (0 : ℝ) < poleBound n := by
    simp only [poleBound]; push_cast; exact_mod_cast (by omega : 0 < 40 * n)
  have hF := log_aeval_normalizedDet_le hn
  rw [eval_normalizedPoly, Real.log_mul normalizingFactor_pos.ne'
    (aeval_normalizedDet_pos n).ne', add_div]
  have hF' : Real.log (aeval zetaFive (normalizedDet n)) / (poleBound n : ℝ) ^ 2 ≤
      energyMargin + (24 * (Real.log (poleBound n) / poleBound n) + 200 / (poleBound n : ℝ)) := by
    rw [div_le_iff₀ (by positivity)]
    have : (energyMargin + (24 * (Real.log (poleBound n) / poleBound n) +
        200 / (poleBound n : ℝ))) * (poleBound n : ℝ) ^ 2 =
        energyMargin * (poleBound n : ℝ) ^ 2 + 24 * poleBound n * Real.log (poleBound n) +
          200 * poleBound n := by
      field_simp
      ring
    rw [this]; exact hF
  linarith

/-- **The combined `K²`-scale bound.** For an integer `M ≥ 40` divisible by `40`,
`limsup_{K → ∞, 40 ∣ K} K⁻² log Q_{K,M}(ξ) ≤ A_M + U`, the `limsup` taken in `EReal`. -/
@[zeta5irr "lem_final_limsup"]
theorem limsup_log_eval_normalizedPoly_div_sq_le (hM : 40 ∣ M) (hM40 : 40 ≤ M) :
    limsup (fun n : ℕ =>
      ((Real.log ((normalizedPoly n M).eval zetaFive) / (poleBound n : ℝ) ^ 2 : ℝ) : EReal))
      atTop ≤ ((AM M + energyMargin : ℝ) : EReal) := by
  refine EReal.le_of_forall_lt_iff_le.mp fun z hz => limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_log_eval_normalizedPoly_div_sq_lt hM hM40
    (EReal.coe_lt_coe_iff.mp hz)] with n hn
  exact EReal.coe_le_coe_iff.mpr hn.le

end Zeta5Irr
