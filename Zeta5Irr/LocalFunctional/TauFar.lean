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
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The far-pole power series `ε_s`

For `s` in a field `K`, the power series
`ε_s = -∑_{k ≥ 0} s^{-k-1} z^k ∈ K[[z]]`
is the expansion of `1 / (z - s)` at `z = 0`: for `s ≠ 0` one has `(z - s) ε_s = 1`.
In the source `K = ℚ_p` and `v_p(s) < 0`, the case of a pole far from the origin, where the
coefficients `s^{-k-1}` tend to `0` $p$-adically.

## Main definitions

* `Zeta5Irr.farEps`: the power series `ε_s = -∑_{k ≥ 0} s^{-k-1} z^k`.

## Main results

* `Zeta5Irr.coeff_farEps`: the `k`-th coefficient of `ε_s` is `-(s⁻¹) ^ (k + 1)`.
* `Zeta5Irr.X_sub_C_mul_farEps`: `(z - s) ε_s = 1` for `s ≠ 0`.
* `Zeta5Irr.farEps_eq_inv`: `ε_s = (z - s)⁻¹` for `s ≠ 0`.

## Implementation notes

* The definition is stated over an arbitrary field, and the hypothesis `v_p(s) < 0` of the
  source is not part of it: the defining formula makes sense for every `s`, and the
  hypothesis is only needed for analytic statements (membership of `ε_s` in a Banach algebra
  of power series and bounds on its norm), which carry it themselves. At `s = 0` the series
  is `0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4: completion at a prime.
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {K : Type*} [Field K]

/-- The power series `ε_s = -∑_{k ≥ 0} s^{-k-1} z^k`, the expansion of `1 / (z - s)` at the
origin. In the source `s ∈ ℚ_p` with `v_p(s) < 0`; this hypothesis is not bundled. -/
@[zeta5irr "def_tau_far"]
noncomputable def farEps (s : K) : K⟦X⟧ :=
  PowerSeries.mk fun k => -(s⁻¹) ^ (k + 1)

/-- The `k`-th coefficient of `ε_s` is `-s^{-k-1}`. -/
@[simp]
theorem coeff_farEps (s : K) (k : ℕ) : coeff k (farEps s) = -(s⁻¹) ^ (k + 1) := by
  simp [farEps]

/-- The constant coefficient of `ε_s` is `-s⁻¹`. -/
@[simp]
theorem constantCoeff_farEps (s : K) : constantCoeff (farEps s) = -s⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_farEps, zero_add, pow_one]

/-- `ε_0 = 0`. -/
@[simp]
theorem farEps_zero : farEps (0 : K) = 0 := by
  ext k
  simp

/-- `ε_s` is the expansion of `1 / (z - s)`: `(z - s) ε_s = 1` for `s ≠ 0`. -/
@[zeta5irr "lem_tau_far_inverse"]
theorem X_sub_C_mul_farEps {s : K} (hs : s ≠ 0) : (X - C s) * farEps s = 1 := by
  ext n
  rw [sub_mul, map_sub, coeff_C_mul, coeff_farEps]
  rcases n with _ | n
  · simp [hs]
  · simp only [coeff_succ_X_mul, coeff_farEps, coeff_one, n.succ_ne_zero, ↓reduceIte]
    linear_combination (s⁻¹) ^ (n + 1) * mul_inv_cancel₀ hs

/-- `ε_s (z - s) = 1` for `s ≠ 0`. -/
theorem farEps_mul_X_sub_C {s : K} (hs : s ≠ 0) : farEps s * (X - C s) = 1 := by
  rw [mul_comm, X_sub_C_mul_farEps hs]

/-- `ε_s = (z - s)⁻¹` for `s ≠ 0`. -/
theorem farEps_eq_inv {s : K} (hs : s ≠ 0) : farEps s = (X - C s)⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hs])).mpr (farEps_mul_X_sub_C hs)

end Zeta5Irr
