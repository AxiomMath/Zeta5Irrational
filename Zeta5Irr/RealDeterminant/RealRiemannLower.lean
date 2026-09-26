/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# A right-endpoint Riemann sum of `log (t + u²)` dominates the integral

For `K > 0`, `m ∈ ℕ` and `t ≥ 0`,
`0 ≤ ∑_{j=1}^m log (t + (j/K)²) - K ∫_0^{m/K} log (t + u²) du`.
Splitting the integral at the grid points `j/K`, each piece
`K ∫_{(j-1)/K}^{j/K} log (t + u²) du` is at most `log (t + (j/K)²)`, because
`u ↦ log (t + u²)` is increasing on `u > 0`.

## Main results

* `Zeta5Irr.intervalIntegrable_log_add_sq`: `u ↦ log (t + u²)` is interval integrable on
  every interval, for every real `t`.
* `Zeta5Irr.mul_integral_le_sum_right`: `K ∫_0^{m/K} f ≤ ∑_{j=1}^m f (j/K)` when `f` is
  bounded on each cell by its value at the right endpoint.
* `Zeta5Irr.integral_log_add_sq_le_sum`: the Riemann-sum lower bound above.

## Implementation notes

* The source takes `K` to be the positive integer `40 n` and `1 ≤ m ≤ K`. The proof uses
  neither: the statement holds for every real `K > 0` and every natural `m`
  (for `m = 0` both sides vanish).
* At `t = 0` the integrand `log (u²)` has a logarithmic singularity at `u = 0`; it is still
  interval integrable, since `t + u²` is analytic and the logarithm of a meromorphic
  function is interval integrable.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.3: the Gram integral and scaling.
-/

@[expose] public section

namespace Zeta5Irr

open Real

/-- For every real `t`, the function `u ↦ log (t + u²)` is interval integrable on every
interval `[a, b]`. -/
theorem intervalIntegrable_log_add_sq (t a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => log (t + u ^ 2)) MeasureTheory.volume a b := by
  apply MeromorphicOn.intervalIntegrable_log
  intro x _
  fun_prop

/-- **Right-endpoint Riemann sums.** If on each cell `(k/K, (k+1)/K)` the function `f` is at
most its value at the right endpoint, then `K ∫_0^{m/K} f ≤ ∑_{j=1}^m f (j/K)`. -/
theorem mul_integral_le_sum_right {f : ℝ → ℝ} {K : ℝ} (hK : 0 < K) (m : ℕ)
    (hint : ∀ a b, IntervalIntegrable f MeasureTheory.volume a b)
    (hf : ∀ k : ℕ, ∀ u ∈ Set.Ioo ((k : ℝ) / K) (((k + 1 : ℕ) : ℝ) / K),
      f u ≤ f (((k + 1 : ℕ) : ℝ) / K)) :
    K * ∫ u in (0 : ℝ)..(m / K), f u ≤ ∑ j ∈ Finset.Icc 1 m, f (j / K) := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun k : ℕ => (k : ℝ) / K) (n := m) (fun k _ => hint _ _)
  simp only [Nat.cast_zero, zero_div] at hsplit
  rw [← hsplit, Finset.mul_sum]
  have hIcc : Finset.Icc 1 m = Finset.image (· + 1) (Finset.range m) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    exact ⟨fun h => ⟨j - 1, by omega, by omega⟩, fun ⟨_, _, _⟩ => by omega⟩
  rw [hIcc, Finset.sum_image (add_left_injective 1).injOn]
  refine Finset.sum_le_sum fun k _ => ?_
  have hle : (k : ℝ) / K ≤ ((k + 1 : ℕ) : ℝ) / K := by
    gcongr
    linarith
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hle (hint _ _)
    (intervalIntegrable_const (c := f (((k + 1 : ℕ) : ℝ) / K))) (hf k)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  have e : ((k + 1 : ℕ) : ℝ) / K - k / K = 1 / K := by
    push_cast
    ring
  rw [e] at h
  calc K * ∫ x in (k : ℝ) / K..((k + 1 : ℕ) : ℝ) / K, f x
      ≤ K * (1 / K * f (((k + 1 : ℕ) : ℝ) / K)) := by gcongr
    _ = _ := by field_simp

/-- **Riemann-sum lower bound.** For `K > 0`, `m ∈ ℕ` and `t ≥ 0`, the right-endpoint
Riemann sum `∑_{j=1}^m log (t + (j/K)²)` dominates `K ∫_0^{m/K} log (t + u²) du`. -/
@[zeta5irr "lem_real_riemann_lower"]
theorem integral_log_add_sq_le_sum {K : ℝ} (hK : 0 < K) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ j ∈ Finset.Icc 1 m, log (t + (j / K) ^ 2) -
      K * ∫ u in (0 : ℝ)..(m / K), log (t + u ^ 2) := by
  rw [sub_nonneg]
  refine mul_integral_le_sum_right hK m (intervalIntegrable_log_add_sq t) fun k u hu => ?_
  have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu.1
  exact log_le_log (by positivity) (by gcongr; exact hu.2.le)

end Zeta5Irr
