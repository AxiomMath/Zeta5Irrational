/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.Iout
public import Zeta5Irr.ExactIntegrals.ExOuterAffine

/-!
# The value of the outer integral

We evaluate the outer integral exactly:
$$I_{\mathrm{out}} = \int_{1/3}^{2\lambda} \Theta(y)\,dy = \frac{127751}{96000}.$$
The rows `(l, r, b, c)` of the table `𝒯` tile `[1/3, 2λ] = [1/3, 37/20]`, and on each open
row the integrand is the affine function `y ↦ b + c y`. Hence `Θ` is interval integrable on
each row, with integral `b (r - l) + (c / 2) (r² - l²)`, and the outer integral is the sum of
these eleven rational numbers.

## Main results

* `Zeta5Irr.intervalIntegrable_and_integral_eq_sum_of_isChain`: integrals over consecutive
  intervals listed in a chain add up to the integral over their union.
* `Zeta5Irr.intervalIntegrable_and_integral_outerIntegrand_of_mem_outerTable`: for a row
  `(l, r, b, c)` of `𝒯`, `Θ` is interval integrable on `[l, r]` with
  `∫_l^r Θ = b (r - l) + (c / 2) (r² - l²)`.
* `Zeta5Irr.outerIntegral_value`: `I_out = 127751 / 96000`.

## Implementation notes

The source splits the integral at the twelve endpoints of `𝒯` using a sum over consecutive
intervals indexed by the natural numbers; here the splitting is an induction along the list
`𝒯` itself, using that each row's right endpoint is the next row's left endpoint.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.4 (The outer integral).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory

/-- If the intervals `[left p, right p]` of a nonempty list `L` are consecutive (the right
endpoint of each is the left endpoint of the next), and `f` is interval integrable on each
with integral `value p`, then `f` is interval integrable from the first left endpoint to the
last right endpoint, with integral the sum of the `value p`. -/
theorem intervalIntegrable_and_integral_eq_sum_of_isChain {α : Type*} {f : ℝ → ℝ}
    {μ : Measure ℝ} {left right value : α → ℝ} :
    ∀ (L : List α) (hL : L ≠ []), L.IsChain (fun p q => right p = left q) →
      (∀ p ∈ L, IntervalIntegrable f μ (left p) (right p) ∧
        ∫ y in left p..right p, f y ∂μ = value p) →
      IntervalIntegrable f μ (left (L.head hL)) (right (L.getLast hL)) ∧
        ∫ y in left (L.head hL)..right (L.getLast hL), f y ∂μ = (L.map value).sum
  | [], hL, _, _ => absurd rfl hL
  | [p], _, _, h => by simpa using h p (by simp)
  | p :: q :: t, _, hc, h => by
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hpq, ht⟩ := hc
    obtain ⟨hi, he⟩ := intervalIntegrable_and_integral_eq_sum_of_isChain (q :: t)
      (List.cons_ne_nil _ _) ht (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨hpi, hpe⟩ := h p (by simp)
    simp only [List.head_cons, List.getLast_cons_cons, List.map_cons, List.sum_cons] at hi he ⊢
    rw [← hpq] at hi he
    refine ⟨hpi.trans hi, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hpi hi, hpe, he]

/-- On a row `(l, r, b, c)` of the outer table `𝒯`, the outer integrand is interval
integrable and `∫_l^r Θ(y) dy = b (r - l) + (c / 2) (r² - l²)`. -/
theorem intervalIntegrable_and_integral_outerIntegrand_of_mem_outerTable {l r b c : ℚ}
    (hp : (l, r, b, c) ∈ outerTable) :
    IntervalIntegrable outerIntegrand volume l r ∧
      ∫ y in (l : ℝ)..r, outerIntegrand y =
        ((b * (r - l) + c / 2 * (r ^ 2 - l ^ 2) : ℚ) : ℝ) := by
  have hlr : (l : ℝ) ≤ r := by exact_mod_cast (outerTable_left_lt_right _ hp).le
  have heq : Set.EqOn (fun y : ℝ => (b : ℝ) + c * y) outerIntegrand (Set.uIoo (l : ℝ) r) := by
    intro y hy
    rw [Set.uIoo_of_le hlr] at hy
    exact (outerIntegrand_eq_of_mem_outerTable hp hy.1 hy.2).symm
  have hc : Continuous fun y : ℝ => (b : ℝ) + c * y := by fun_prop
  refine ⟨(hc.intervalIntegrable _ _).congr_uIoo heq, ?_⟩
  rw [← intervalIntegral.integral_congr_uIoo heq]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, integral_id]
  push_cast
  ring

/-- The value of the outer integral: `I_out = 127751 / 96000`. -/
@[zeta5irr "lem_Iout_value"]
theorem outerIntegral_value : outerIntegral = 127751 / 96000 := by
  have hc : outerTable.IsChain (fun p q => ((p.2.1 : ℚ) : ℝ) = (q.1 : ℚ)) :=
    outerTable_isChain.imp fun _ _ h => congrArg _ h
  have h := (intervalIntegrable_and_integral_eq_sum_of_isChain (f := outerIntegrand)
    (μ := volume) (left := fun p : ℚ × ℚ × ℚ × ℚ => (p.1 : ℝ))
    (right := fun p => (p.2.1 : ℝ))
    (value := fun p =>
      ((p.2.2.1 * (p.2.1 - p.1) + p.2.2.2 / 2 * (p.2.1 ^ 2 - p.1 ^ 2) : ℚ) : ℝ))
    outerTable (by simp [outerTable]) hc
    (fun p hp => intervalIntegrable_and_integral_outerIntegrand_of_mem_outerTable hp)).2
  rw [outerIntegral_eq, show (1 / 3 : ℝ) = ((1 / 3 : ℚ) : ℝ) by push_cast; rfl,
    show (37 / 20 : ℝ) = ((37 / 20 : ℚ) : ℝ) by push_cast; rfl, ← outerTable_head_left,
    ← outerTable_getLast_right, h]
  simp only [outerTable, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

end Zeta5Irr
