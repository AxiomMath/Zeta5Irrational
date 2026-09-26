/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormPntOuter

/-!
# Prime sums weighted by a piecewise continuous function

Let `0 < u` and let `f` be piecewise continuous on `[u, v]`. As a consequence of the prime
number theorem,
`K⁻² ∑_{K/v < p ≤ K/u} p f(K/p) log p → ∫_u^v f(x) x⁻³ dx` as `K → ∞`, the sum being over
primes. The condition `K/v < p ≤ K/u` says `u ≤ K/p < v`, so every term evaluates `f` inside
`[u, v]`.

The function `g(y) = y f(1/y)` is piecewise continuous on `[1/v, 1/u]`, and
`K⁻² p f(K/p) log p = K⁻¹ g(p/K) log p`. So the limit is the prime sum in the outer variable
(`Zeta5Irr.PiecewiseContinuousOn.tendsto_sum_prime_mul_log_div_atTop`) for `g` on
`[1/v, 1/u]`, whose value `∫_{1/v}^{1/u} g(y) dy` is `∫_u^v f(x) x⁻³ dx` by the substitution
`y = 1/x`.

## Main results

* `Zeta5Irr.integral_mul_comp_inv`: `∫_{1/v}^{1/u} y f(1/y) dy = ∫_u^v f(x) x⁻³ dx`.
* `Zeta5Irr.PiecewiseContinuousOn.tendsto_sum_prime_mul_log_div_sq`: the main limit.

## Implementation notes

* The source takes the interval `[3, M]` with `M ≥ 40` an integer, and `K` an integer. The
  statement here holds for every interval `[u, v]` with `0 < u` and along real `K → ∞`; the
  source's statement is the case `u = 3`, `v = M`.
* For `K ≥ 0` a natural number `p` satisfies `K/v < p ≤ K/u` exactly when
  `⌊K/v⌋₊ < p ≤ ⌊K/u⌋₊`, so the sum is written over the primes of
  `Finset.Ioc ⌊K / v⌋₊ ⌊K / u⌋₊`.
* The source splits the sum at every partition point and bounds `limsup` and `liminf`
  separately; here the result is instead reduced to the outer-variable prime sum by the
  substitution `y = 1/x`, which reverses the partition.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.7 (The prime number theorem).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology MeasureTheory Set

/-- The substitution `y = 1/x`: for `0 < u ≤ v`,
`∫_{1/v}^{1/u} y f(1/y) dy = ∫_u^v f(x) x⁻³ dx`. -/
theorem integral_mul_comp_inv (f : ℝ → ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ y in v⁻¹..u⁻¹, y * f y⁻¹ = ∫ x in u..v, f x / x ^ 3 := by
  have himg : Inv.inv '' Icc u v = Icc v⁻¹ u⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨inv_anti₀ (hu.trans_le hx.1) hx.2, inv_anti₀ hu hx.1⟩
    · rintro ⟨h1, h2⟩
      have hy0 : 0 < y := (inv_pos.2 (hu.trans_le huv)).trans_le h1
      exact ⟨y⁻¹, ⟨(le_inv_comm₀ hu hy0).2 h2, (inv_le_comm₀ hy0 (hu.trans_le huv)).2 h1⟩,
        inv_inv y⟩
  have h := integral_image_eq_integral_abs_deriv_smul (s := Icc u v) measurableSet_Icc
    (f := Inv.inv) (f' := fun x => -(x ^ 2)⁻¹)
    (fun x hx => (hasDerivAt_inv (hu.trans_le hx.1).ne').hasDerivWithinAt) inv_injective.injOn
    (fun y => y * f y⁻¹)
  rw [himg] at h
  rw [intervalIntegral.integral_of_le (inv_anti₀ hu huv), intervalIntegral.integral_of_le huv,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, h]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  have hx0 : 0 < x := hu.trans_le hx.1
  simp only [smul_eq_mul, abs_neg, inv_inv, abs_of_pos (inv_pos.2 (pow_pos hx0 2))]
  field_simp

/-- **Prime sums weighted by a piecewise continuous function.** Let `0 < u` and let `f` be
piecewise continuous on `[u, v]`. Then
`K⁻² ∑_{K/v < p ≤ K/u} p f(K/p) log p → ∫_u^v f(x) x⁻³ dx` as `K → ∞`, the sum being over
primes. -/
@[zeta5irr "lem_partial_sum_pnt"]
theorem PiecewiseContinuousOn.tendsto_sum_prime_mul_log_div_sq {f : ℝ → ℝ} {u v : ℝ}
    (hu : 0 < u) (hf : PiecewiseContinuousOn f u v) :
    Tendsto (fun K : ℝ ↦
      (∑ p ∈ Finset.Ioc ⌊K / v⌋₊ ⌊K / u⌋₊ with p.Prime, (p : ℝ) * f (K / p) * Real.log p) /
        K ^ 2) atTop (𝓝 (∫ x in u..v, f x / x ^ 3)) := by
  have huv := hf.lt
  have h := (hf.mul_comp_inv hu).tendsto_sum_prime_mul_log_div_atTop
    (inv_pos.2 (hu.trans huv)).le
  rw [integral_mul_comp_inv f hu huv.le] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  rw [inv_mul_eq_div, inv_mul_eq_div, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inv_div]
  field_simp

end Zeta5Irr
