/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

/-!
# Abel summation against Chebyshev's `θ`

Let `Y ≥ 1` and let `φ` be continuously differentiable on `[1, Y]`. Summation by parts against
Chebyshev's function `θ(t) = ∑_{p ≤ t} log p` gives
`∑_{p ≤ Y} φ(p) log p = φ(Y) θ(Y) - ∫_1^Y φ'(t) θ(t) dt`.

The proof writes `θ(t) = ∑_{p ≤ Y} log p · 𝟙_{[p, ∞)}(t)` for `t ∈ [1, Y]`, exchanges the integral
with this finite sum, and evaluates `∫_1^Y φ' · 𝟙_{[p, ∞)} = ∫_p^Y φ' = φ(Y) - φ(p)` by the
fundamental theorem of calculus.

## Main results

* `Zeta5Irr.integral_indicator_Ici_eq_sub`: `∫_a^c 𝟙_{[b, ∞)} φ' = φ(c) - φ(b)` for `a ≤ b ≤ c`.
* `Zeta5Irr.theta_eq_sum_primesLE_ite`: for `0 ≤ t ≤ Y`,
  `θ(t) = ∑_{p ≤ Y} (if p ≤ t then log p else 0)`.
* `Zeta5Irr.sum_primesLE_log_smul_eq_sub_integral`: Abel summation against `θ`, for `φ` valued in
  a real Banach space.
* `Zeta5Irr.sum_primesLE_mul_log_eq_sub_integral`: the real-valued statement of the source.

## Implementation notes

* The source asks `φ` to be continuously differentiable on `[1, Y]`. We only use that `φ` is
  continuous on `[1, Y]`, differentiable on `(1, Y)` with derivative `φ'`, and that `φ'` is
  integrable on `[1, Y]`; all three follow from the source's hypothesis. The derivative is
  passed as a separate function `φ'` rather than as `deriv φ`.
* The general form allows `φ` to take values in any real Banach space `E`, the products
  `φ(p) log p` and `φ'(t) θ(t)` becoming scalar multiplications.
* The primes `p ≤ Y` are enumerated as `Nat.primesLE ⌊Y⌋₊`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.7 (The prime number theorem).
-/

@[expose] public section

namespace Zeta5Irr

open Real MeasureTheory Set Chebyshev
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If `φ` is continuous on `[a, c]` with derivative `φ'` on `(a, c)`, and `φ'` is integrable on
`[a, c]`, then for `a ≤ b ≤ c` the integral over `[a, c]` of `φ'` cut off below `b` is
`φ c - φ b`. -/
theorem integral_indicator_Ici_eq_sub {φ φ' : ℝ → E} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hφ : ContinuousOn φ (Icc a c)) (hφ' : ∀ t ∈ Ioo a c, HasDerivAt φ (φ' t) t)
    (hint : IntervalIntegrable φ' volume a c) :
    ∫ t in a..c, (Ici b).indicator φ' t = φ c - φ b := by
  have hind : IntervalIntegrable ((Ici b).indicator φ') volume a c :=
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hint).indicator measurableSet_Ici)
  have hb : b ∈ [[a, c]] := by rw [uIcc_of_le (hab.trans hbc)]; exact ⟨hab, hbc⟩
  obtain ⟨h1, h2⟩ := (IntervalIntegrable.trans_iff hb).1 hind
  have hbc' : IntervalIntegrable φ' volume b c := ((IntervalIntegrable.trans_iff hb).1 hint).2
  have h1ae : ∀ᵐ t ∂volume, t ∈ Ι a b → (Ici b).indicator φ' t = 0 := by
    filter_upwards [Measure.ae_ne volume b] with t htb ht
    rw [uIoc_of_le hab] at ht
    exact indicator_of_notMem (fun h : b ≤ t => htb (le_antisymm ht.2 h)) _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    intervalIntegral.integral_congr_ae h1ae, intervalIntegral.integral_zero, zero_add,
    intervalIntegral.integral_congr (g := φ') (fun t ht => by
      rw [uIcc_of_le hbc] at ht; exact indicator_of_mem (show b ≤ t from ht.1) _)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbc
    (hφ.mono (Icc_subset_Icc hab le_rfl))
    (fun t ht => hφ' t ⟨hab.trans_lt ht.1, ht.2⟩) hbc'

/-- For `0 ≤ t ≤ Y`, Chebyshev's `θ t` is the sum over the primes `p ≤ Y` of `log p` if `p ≤ t`,
and `0` otherwise. -/
theorem theta_eq_sum_primesLE_ite {Y t : ℝ} (ht0 : 0 ≤ t) (htY : t ≤ Y) :
    θ t = ∑ p ∈ Nat.primesLE ⌊Y⌋₊, if (p : ℝ) ≤ t then log p else 0 := by
  rw [← Finset.sum_filter, theta_eq_sum_primesLE]
  congr 1
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_filter, Nat.le_floor_iff ht0]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Nat.le_floor (h1.trans htY), h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩
    exact ⟨h1, h2⟩

/-- **Abel summation against Chebyshev's `θ`.** If `1 ≤ Y`, `φ` is continuous on `[1, Y]` with
derivative `φ'` on `(1, Y)`, and `φ'` is integrable on `[1, Y]`, then
`∑_{p ≤ Y} log p • φ p = θ Y • φ Y - ∫_1^Y θ t • φ' t`. -/
theorem sum_primesLE_log_smul_eq_sub_integral {φ φ' : ℝ → E} {Y : ℝ} (hY : 1 ≤ Y)
    (hφ : ContinuousOn φ (Icc 1 Y)) (hφ' : ∀ t ∈ Ioo 1 Y, HasDerivAt φ (φ' t) t)
    (hint : IntervalIntegrable φ' volume 1 Y) :
    ∑ p ∈ Nat.primesLE ⌊Y⌋₊, log p • φ p = θ Y • φ Y - ∫ t in 1..Y, θ t • φ' t := by
  have hp : ∀ p ∈ Nat.primesLE ⌊Y⌋₊, (1 : ℝ) ≤ p ∧ (p : ℝ) ≤ Y := fun p hp => by
    rw [Nat.mem_primesLE] at hp
    exact ⟨by exact_mod_cast hp.2.one_lt.le, (Nat.le_floor_iff (zero_le_one.trans hY)).1 hp.1⟩
  have hind : ∀ p : ℕ, IntervalIntegrable ((Ici (p : ℝ)).indicator φ') volume 1 Y := fun p =>
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hint).indicator measurableSet_Ici)
  have key : ∫ t in 1..Y, θ t • φ' t =
      ∑ p ∈ Nat.primesLE ⌊Y⌋₊, log p • (φ Y - φ p) := by
    rw [intervalIntegral.integral_congr (g := fun t => ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        log p • (Ici (p : ℝ)).indicator φ' t) (fun t ht => by
      rw [uIcc_of_le hY] at ht
      simp only [theta_eq_sum_primesLE_ite (zero_le_one.trans ht.1) ht.2, Finset.sum_smul]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h : (p : ℝ) ≤ t
      · simp [h]
      · simp [h]),
      intervalIntegral.integral_finsetSum
        (f := fun (p : ℕ) t => log p • (Ici (p : ℝ)).indicator φ' t)
        fun p _ => (hind p).smul (log p)]
    refine Finset.sum_congr rfl fun p hpY => ?_
    rw [intervalIntegral.integral_smul,
      integral_indicator_Ici_eq_sub (hp p hpY).1 (hp p hpY).2 hφ hφ' hint]
  rw [key, theta_eq_sum_primesLE, Finset.sum_smul]
  simp only [smul_sub, Finset.sum_sub_distrib, sub_sub_cancel]

/-- **Abel summation against Chebyshev's `θ`.** Let `Y ≥ 1` and let `φ : ℝ → ℝ` be continuous on
`[1, Y]` with derivative `φ'` on `(1, Y)`, `φ'` integrable on `[1, Y]` (e.g. `φ` continuously
differentiable on `[1, Y]`). Then `∑_{p ≤ Y} φ(p) log p = φ(Y) θ(Y) - ∫_1^Y φ'(t) θ(t) dt`. -/
@[zeta5irr "lem_norm_abel"]
theorem sum_primesLE_mul_log_eq_sub_integral {φ φ' : ℝ → ℝ} {Y : ℝ} (hY : 1 ≤ Y)
    (hφ : ContinuousOn φ (Icc 1 Y)) (hφ' : ∀ t ∈ Ioo 1 Y, HasDerivAt φ (φ' t) t)
    (hint : IntervalIntegrable φ' volume 1 Y) :
    ∑ p ∈ Nat.primesLE ⌊Y⌋₊, φ p * log p = φ Y * θ Y - ∫ t in 1..Y, φ' t * θ t := by
  simpa only [smul_eq_mul, mul_comm] using
    sum_primesLE_log_smul_eq_sub_integral hY hφ hφ' hint

end Zeta5Irr
