/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormPprime
public import Zeta5Irr.PrimeSum.NormP2Cont
public import Zeta5Irr.PrimeSum.NormP2prime
public import Zeta5Irr.PrimeSum.NormP2Bound
public import Zeta5Irr.PrimeSum.NormTailIntegrable
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-!
# The tail integral of `R(x) / x³` by parts

For every real `x₀ > 0`, and in particular for every `x₀ ≥ 3`,
`∫_{x₀}^∞ R(x) x⁻³ dx = -λ/x₀ - 𝒫(x₀)/x₀² + 2923/(240 x₀²) - 2 𝒫₂(x₀)/x₀³
  + 6 ∫_{x₀}^∞ 𝒫₂(x) x⁻⁴ dx + ∫_{x₀}^∞ 𝓔(x) x⁻³ dx`,
where `R` is the inner limiting function, `𝒫` and `𝒫₂` are the first and second periodic
antiderivatives, `𝓔` is the error term of the splitting `R(x) = x Φ(x) + 𝓔(x)` and
`λ = 37/40`.

By the splitting, the left-hand side is `∫ Φ(x) x⁻² dx + ∫ 𝓔(x) x⁻³ dx`. The function
`F(x) = 𝒫(x)/x² + λ/x + 2 𝒫₂(x)/x³ - (2923/240)/x²` is continuous on `(0, ∞)`, tends to `0`
at infinity, and away from the countable set `ℤ ∪ α⁻¹ℤ` has derivative
`F'(x) = Φ(x)/x² - 6 𝒫₂(x)/x⁴`, since `𝒫' = Φ + λ` and `𝒫₂' = 𝒫 - 2923/240` there. The
fundamental theorem of calculus off a countable set then gives
`∫_{x₀}^∞ F' = -F(x₀)`, which is the claim.

## Main results

* `Zeta5Irr.integral_Ioi_eq_sub_of_hasDerivAt_off_countable`: the fundamental theorem of
  calculus on `(a, ∞)` for a function continuous on `[a, ∞)`, differentiable off a countable
  set, with integrable derivative and a limit at infinity.
* `Zeta5Irr.integral_Ioi_innerLimitingR_div_pow_three_eq`: the integration-by-parts formula
  for the tail integral of `R(x) / x³`.

## Implementation notes

* The source states the result for `x₀ ≥ 3`; only `x₀ > 0` is used.
* The source integrates by parts twice, first with `𝒫(x)/x²` and then with `𝒫₂(x)/x³`, each
  time on `[x₀, Y]` followed by `Y → ∞`. Here the two steps are combined into a single
  application of the fundamental theorem of calculus to the function `F` above, whose
  derivative is the sum of the two integrands; the resulting identity is the same.
* The integrability of `𝓔(x)/x³` on `(x₀, ∞)` is obtained from that of `R(x)/x³` and of
  `Φ(x)/x²` via the splitting, rather than from the piecewise continuity of `𝓔`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.9 (The tail integral).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Filter Topology

/-- **Fundamental theorem of calculus on `(a, ∞)`, off a countable set.** If `f` is continuous
on `[a, ∞)`, has derivative `f'` at every point of `(a, ∞)` outside a countable set, `f'` is
integrable on `(a, ∞)` and `f` tends to `L` at infinity, then `∫_{(a, ∞)} f' = L - f a`. -/
theorem integral_Ioi_eq_sub_of_hasDerivAt_off_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E} {a : ℝ} {L : E} {s : Set ℝ}
    (hs : s.Countable) (hcont : ContinuousOn f (Ici a))
    (hderiv : ∀ x ∈ Ioi a \ s, HasDerivAt f (f' x) x) (hint : IntegrableOn f' (Ioi a))
    (hf : Tendsto f atTop (𝓝 L)) :
    ∫ x in Ioi a, f' x = L - f a := by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a hint tendsto_id) ?_
  refine Tendsto.congr' ?_ (hf.sub_const (f a))
  filter_upwards [eventually_ge_atTop a] with b hb
  refine (integral_eq_of_hasDerivAt_off_countable_of_le f f' hb hs
    (hcont.mono Icc_subset_Ici_self) (fun x hx => hderiv x ⟨hx.1.1, hx.2⟩) ?_).symm
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).2 (hint.mono_set Ioc_subset_Ioi_self)

/-- A bounded measurable function divided by `x ^ k`, `k ≥ 2`, is integrable on `(c, ∞)` for
`c > 0`. -/
theorem integrableOn_Ioi_div_pow {g : ℝ → ℝ} {c C : ℝ} {k : ℕ} (hg : AEStronglyMeasurable g)
    (hC : ∀ x, |g x| ≤ C) (hk : 2 ≤ k) (hc : 0 < c) :
    IntegrableOn (fun x => g x / x ^ k) (Ioi c) := by
  have hI : IntegrableOn (fun x : ℝ => C * x ^ (-(k : ℝ))) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                                     linarith) hc).const_mul C
  refine hI.mono' ((hg.aemeasurable.div (by fun_prop)).aestronglyMeasurable.restrict) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun x hx => ?_
  have hx0 : 0 < x := hc.trans hx
  rw [Real.rpow_neg hx0.le, Real.rpow_natCast, Real.norm_eq_abs, abs_div,
    abs_of_pos (pow_pos hx0 k), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hC x) (pow_pos hx0 k).le

/-- For `c > 0` and `k ≥ 2`, `∫_{(c, ∞)} 1 / x ^ k dx = 1 / ((k - 1) c ^ (k - 1))`. -/
theorem integral_Ioi_one_div_pow {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 2 ≤ k) :
    ∫ x in Ioi c, 1 / x ^ k = 1 / ((k - 1) * c ^ (k - 1)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x : ℝ => x ^ (-(k : ℝ)))
    (fun x hx => by simp only; rw [Real.rpow_neg (hc.trans hx).le, Real.rpow_natCast, one_div]),
    integral_Ioi_rpow_of_lt (by linarith) hc]
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [show -(k : ℝ) + 1 = -((k - 1 : ℕ) : ℝ) by rw [hk1]; ring, Real.rpow_neg hc.le,
    Real.rpow_natCast, hk1]
  have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  field_simp

/-- If `C ≤ g` on `(c, ∞)`, `c > 0`, `k ≥ 2` and `g(x) / x ^ k` is integrable on `(c, ∞)`, then
`C / ((k - 1) c ^ (k - 1)) ≤ ∫_{(c, ∞)} g(x) / x ^ k dx`. -/
theorem le_setIntegral_Ioi_div_pow {g : ℝ → ℝ} {c C : ℝ} {k : ℕ} (hc : 0 < c) (hk : 2 ≤ k)
    (hint : IntegrableOn (fun x => g x / x ^ k) (Ioi c)) (hg : ∀ x, c < x → C ≤ g x) :
    C / ((k - 1) * c ^ (k - 1)) ≤ ∫ x in Ioi c, g x / x ^ k := by
  rw [← mul_one_div, ← integral_Ioi_one_div_pow hc hk, ← integral_const_mul]
  refine setIntegral_mono_on ((integrableOn_Ioi_div_pow (g := fun _ => 1) (C := 1)
    aestronglyMeasurable_const (fun _ => by simp) hk hc).const_mul C) hint measurableSet_Ioi
    fun x hx => ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (hg x hx) (pow_pos (hc.trans hx) k).le

/-- If `g ≤ C` on `(c, ∞)` with `C ≥ 0`, `c > 0` and `k ≥ 2`, then
`∫_{(c, ∞)} g(x) / x ^ k dx ≤ C / ((k - 1) c ^ (k - 1))`. No integrability of `g` is assumed:
when the integrand is not integrable the integral is `0`. -/
theorem setIntegral_Ioi_div_pow_le {g : ℝ → ℝ} {c C : ℝ} {k : ℕ} (hc : 0 < c) (hk : 2 ≤ k)
    (hC : 0 ≤ C) (hg : ∀ x, c < x → g x ≤ C) :
    ∫ x in Ioi c, g x / x ^ k ≤ C / ((k - 1) * c ^ (k - 1)) := by
  by_cases hint : IntegrableOn (fun x => g x / x ^ k) (Ioi c)
  · have h := le_setIntegral_Ioi_div_pow (g := -g) (C := -C) hc hk (by simpa [neg_div] using
      hint.neg) fun x hx => neg_le_neg (hg x hx)
    simp only [Pi.neg_apply, neg_div, integral_neg] at h
    linarith
  · rw [integral_undef hint]
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : 0 < c ^ (k - 1) := pow_pos hc _
    exact div_nonneg hC (mul_nonneg (by linarith) this.le)

/-- A bounded function divided by `x ^ k`, `k ≠ 0`, tends to `0` at infinity. -/
theorem tendsto_div_pow_atTop_zero {g : ℝ → ℝ} {C : ℝ} {k : ℕ} (hC : ∀ x, |g x| ≤ C)
    (hk : k ≠ 0) : Tendsto (fun x => g x / x ^ k) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (Tendsto.div_atTop (tendsto_const_nhds (x := C)) (tendsto_pow_atTop hk))
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx k)]
  exact div_le_div_of_nonneg_right (hC x) (pow_pos hx k).le

/-- A crude bound on the first periodic antiderivative: `|𝒫(x)| ≤ 75`. -/
theorem abs_firstPeriodicAntideriv_le (x : ℝ) : |firstPeriodicAntideriv x| ≤ 75 := by
  have h (t : ℝ) : 0 ≤ Int.fract t * (1 - Int.fract t) ∧ Int.fract t * (1 - Int.fract t) ≤ 1 := by
    have := Int.fract_nonneg t
    have := Int.fract_lt_one t
    constructor <;> nlinarith
  have hl : (0 : ℝ) < orderRatio := by norm_num [orderRatio]
  have hl1 : (orderRatio : ℝ) ≤ 1 := by norm_num [orderRatio]
  obtain ⟨h1, h2⟩ := h ((innerRatio : ℝ) * x)
  obtain ⟨h3, h4⟩ := h x
  unfold firstPeriodicAntideriv
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hl.le h3]

/-- **The tail integral by parts.** For every `x₀ > 0` (the source takes `x₀ ≥ 3`),
`∫_{x₀}^∞ R(x)/x³ dx = -λ/x₀ - 𝒫(x₀)/x₀² + 2923/(240 x₀²) - 2 𝒫₂(x₀)/x₀³
  + 6 ∫_{x₀}^∞ 𝒫₂(x)/x⁴ dx + ∫_{x₀}^∞ 𝓔(x)/x³ dx`. -/
@[zeta5irr "lem_tail_ibp"]
theorem integral_Ioi_innerLimitingR_div_pow_three_eq {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∫ x in Ioi x₀, innerLimitingR x / x ^ 3 =
      -((orderRatio : ℝ) / x₀) - firstPeriodicAntideriv x₀ / x₀ ^ 2 + 2923 / (240 * x₀ ^ 2) -
        2 * secondPeriodicAntideriv x₀ / x₀ ^ 3 +
        6 * (∫ x in Ioi x₀, secondPeriodicAntideriv x / x ^ 4) +
        ∫ x in Ioi x₀, innerSplitError x / x ^ 3 := by
  set P := firstPeriodicAntideriv
  set P₂ := secondPeriodicAntideriv
  set Φ := sawtoothSlope
  set l : ℝ := (orderRatio : ℝ) with hl
  set F : ℝ → ℝ := fun x => P x / x ^ 2 + l / x + 2 * P₂ x / x ^ 3 - 2923 / 240 / x ^ 2
    with hF
  have hΦ : IntegrableOn (fun x => Φ x / x ^ 2) (Ioi x₀) :=
    integrableOn_Ioi_div_pow measurable_sawtoothSlope.aestronglyMeasurable
      abs_sawtoothSlope_le_eighteen le_rfl hx₀
  have hP₂ : IntegrableOn (fun x => P₂ x / x ^ 4) (Ioi x₀) :=
    integrableOn_Ioi_div_pow continuous_secondPeriodicAntideriv.aestronglyMeasurable
      abs_secondPeriodicAntideriv_le (by norm_num) hx₀
  have hR : IntegrableOn (fun x => innerLimitingR x / x ^ 3) (Ioi x₀) :=
    (integrableOn_innerLimitingR_div_pow_three_Ici hx₀).mono_set Ioi_subset_Ici_self
  have hsplit : EqOn (fun x => innerLimitingR x / x ^ 3)
      (fun x => Φ x / x ^ 2 + innerSplitError x / x ^ 3) (Ioi x₀) := by
    intro x hx
    have hx0 : x ≠ 0 := (hx₀.trans hx).ne'
    simp only [innerLimitingR_eq, Φ]
    field_simp
  have hE : IntegrableOn (fun x => innerSplitError x / x ^ 3) (Ioi x₀) := by
    refine (hR.sub hΦ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have := hsplit hx
    simp only [Pi.sub_apply] at this ⊢
    rw [this]
    ring
  have hF' : ∫ x in Ioi x₀, (Φ x / x ^ 2 - 6 * (P₂ x / x ^ 4)) = 0 - F x₀ := by
    refine integral_Ioi_eq_sub_of_hasDerivAt_off_countable
      ((countable_range ((↑) : ℤ → ℝ)).union
        (countable_range fun m : ℤ => (innerRatio : ℝ)⁻¹ * m)) ?_ ?_
      (hΦ.sub (hP₂.const_mul 6)) ?_
    · intro x hx
      have hx0 : x ≠ 0 := (hx₀.trans_le hx).ne'
      simp only [hF]
      have hP := continuous_firstPeriodicAntideriv.continuousAt (x := x)
      have hP₂ := continuous_secondPeriodicAntideriv.continuousAt (x := x)
      refine ContinuousAt.continuousWithinAt ?_
      refine ((((hP.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).add
        (continuousAt_const.div continuousAt_id hx0)).add
        ((continuousAt_const.mul hP₂).div (continuousAt_id.pow 3) (pow_ne_zero 3 hx0))).sub
        (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)))
    · rintro x ⟨hx, hxs⟩
      have hx0 : x ≠ 0 := (hx₀.trans hx).ne'
      simp only [mem_union, not_or] at hxs
      obtain ⟨hs₁, hs₂⟩ := hxs
      have hα : (innerRatio : ℝ) ≠ 0 := by norm_num [innerRatio]
      have hαx : (innerRatio : ℝ) * x ∉ range ((↑) : ℤ → ℝ) := by
        rintro ⟨m, hm⟩
        exact hs₂ ⟨m, by simp only; rw [hm, inv_mul_cancel_left₀ hα]⟩
      have h1 := (hasDerivAt_firstPeriodicAntideriv hs₁ hαx).div (hasDerivAt_pow 2 x)
        (pow_ne_zero 2 hx0)
      have h2 := (hasDerivAt_const x l).div (hasDerivAt_id x) hx0
      have h3 := ((hasDerivAt_secondPeriodicAntideriv (fun m h => hs₁ ⟨m, h.symm⟩)
        (fun m h => hs₂ ⟨m, h.symm⟩)).const_mul 2).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx0)
      have h4 := (hasDerivAt_const x (2923 / 240 : ℝ)).div (hasDerivAt_pow 2 x)
        (pow_ne_zero 2 hx0)
      convert ((h1.add h2).add h3).sub h4 using 1
      · ext y
        simp only [F, P, P₂, l, Pi.add_apply, Pi.sub_apply, Pi.div_apply, id]
      · simp only [Φ, P₂, id]
        field_simp
        ring
    · have := (((tendsto_div_pow_atTop_zero abs_firstPeriodicAntideriv_le two_ne_zero).add
        (tendsto_div_pow_atTop_zero (g := fun _ => l) (C := |l|) (fun _ => le_rfl)
          one_ne_zero)).add
        (tendsto_div_pow_atTop_zero (g := fun x => 2 * P₂ x) (C := 2 * 16)
          (fun x => by rw [abs_mul, abs_two]; linarith [abs_secondPeriodicAntideriv_le x])
          three_ne_zero)).sub
        (tendsto_div_pow_atTop_zero (g := fun _ => (2923 / 240 : ℝ)) (C := 2923 / 240)
          (fun _ => by norm_num) two_ne_zero)
      simpa [hF] using this
  rw [integral_sub hΦ (hP₂.const_mul 6), integral_const_mul] at hF'
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hΦ hE]
  simp only [hF] at hF'
  linear_combination hF'

end Zeta5Irr
