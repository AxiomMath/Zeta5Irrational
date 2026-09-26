/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.LocalEstimates.OutMuX0
public import Mathlib.RingTheory.PiTensorProduct

/-!
# The integral part of the outer form

Let `p` be a prime and fix the parameters `N = 3 n` and `K = 40 n`. For `A₁, A₂ ∈ ℚ[t]` the
integral part of the outer form is
`Φ₀(A₁, A₂) = μ_{0,X}(D_N(t) ^ 5 A₁(t) A₂(t); {N + 1, …, K}) ∈ ℚ_p[X]`,
the integral part `μ_{0,X}` of the functional on the far poles `N < j ≤ K`, applied to
`D_N ^ 5 A₁ A₂`. Since `μ_{0,X}(·; S)` is `ℚ`-linear and multiplication in `ℚ[t]` is
commutative, `Φ₀` is a symmetric `ℚ`-bilinear form with values in `ℚ_p[X]`.

## Main definitions

* `Zeta5Irr.outerIntegralForm`: `Φ₀(A₁, A₂) = μ_{0,X}(D_N ^ 5 A₁ A₂; {N + 1, …, K})`.

## Main results

* `Zeta5Irr.outerIntegralForm_comm`: `Φ₀(A₁, A₂) = Φ₀(A₂, A₁)`.
* `Zeta5Irr.outerIntegralForm_add_left`, `Zeta5Irr.outerIntegralForm_add_right`,
  `Zeta5Irr.outerIntegralForm_smul_left`, `Zeta5Irr.outerIntegralForm_smul_right`:
  `Φ₀` is `ℚ`-bilinear.
* `Zeta5Irr.outerIntegralForm_sum_left`, `Zeta5Irr.outerIntegralForm_sum_right`:
  `Φ₀` commutes with finite sums in each argument.

## Implementation notes

* `Φ₀` is a plain function of two polynomial arguments rather than a bundled bilinear map;
  bilinearity and symmetry are separate lemmas. The parameters enter through `n`, with
  `N = innerDegree n` and `K = poleBound n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7: the outer range, the integral part and its
  correction.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The integral part of the outer form,
`Φ₀(A₁, A₂) = μ_{0,X}(D_N ^ 5 A₁ A₂; {N + 1, …, K})` with `N = 3 n` and `K = 40 n`. -/
@[zeta5irr "def_out_form0"]
noncomputable def outerIntegralForm (A₁ A₂ : ℚ[X]) : ℚ_[p][X] :=
  truncatedPoleFunctional p (Icc (innerDegree n + 1) (poleBound n))
    (poleProductRange (innerDegree n) ℚ ^ 5 * A₁ * A₂)

/-- `Φ₀` is symmetric. -/
theorem outerIntegralForm_comm (A₁ A₂ : ℚ[X]) :
    outerIntegralForm p n A₁ A₂ = outerIntegralForm p n A₂ A₁ := by
  rw [outerIntegralForm, outerIntegralForm, mul_right_comm]

/-- `Φ₀(0, A) = 0`. -/
@[simp]
theorem outerIntegralForm_zero_left (A : ℚ[X]) : outerIntegralForm p n 0 A = 0 := by
  simp [outerIntegralForm]

/-- `Φ₀(A, 0) = 0`. -/
@[simp]
theorem outerIntegralForm_zero_right (A : ℚ[X]) : outerIntegralForm p n A 0 = 0 := by
  simp [outerIntegralForm]

/-- `Φ₀` is additive in its first argument. -/
theorem outerIntegralForm_add_left (A₁ A₁' A₂ : ℚ[X]) :
    outerIntegralForm p n (A₁ + A₁') A₂ =
      outerIntegralForm p n A₁ A₂ + outerIntegralForm p n A₁' A₂ := by
  simp only [outerIntegralForm, mul_add, add_mul, map_add]

/-- `Φ₀` is additive in its second argument. -/
theorem outerIntegralForm_add_right (A₁ A₂ A₂' : ℚ[X]) :
    outerIntegralForm p n A₁ (A₂ + A₂') =
      outerIntegralForm p n A₁ A₂ + outerIntegralForm p n A₁ A₂' := by
  simp only [outerIntegralForm, mul_add, map_add]

/-- `Φ₀` is `ℚ`-homogeneous in its first argument. -/
theorem outerIntegralForm_smul_left (c : ℚ) (A₁ A₂ : ℚ[X]) :
    outerIntegralForm p n (c • A₁) A₂ = c • outerIntegralForm p n A₁ A₂ := by
  simp only [outerIntegralForm, mul_smul_comm, smul_mul_assoc, map_smul]

/-- `Φ₀` is `ℚ`-homogeneous in its second argument. -/
theorem outerIntegralForm_smul_right (c : ℚ) (A₁ A₂ : ℚ[X]) :
    outerIntegralForm p n A₁ (c • A₂) = c • outerIntegralForm p n A₁ A₂ := by
  simp only [outerIntegralForm, mul_smul_comm, map_smul]

/-- `Φ₀` commutes with finite sums in its first argument. -/
theorem outerIntegralForm_sum_left {ι : Type*} (s : Finset ι) (A : ι → ℚ[X]) (B : ℚ[X]) :
    outerIntegralForm p n (∑ i ∈ s, A i) B = ∑ i ∈ s, outerIntegralForm p n (A i) B := by
  simp only [outerIntegralForm, mul_sum, sum_mul, map_sum]

/-- `Φ₀` commutes with finite sums in its second argument. -/
theorem outerIntegralForm_sum_right {ι : Type*} (s : Finset ι) (A : ℚ[X]) (B : ι → ℚ[X]) :
    outerIntegralForm p n A (∑ i ∈ s, B i) = ∑ i ∈ s, outerIntegralForm p n A (B i) := by
  simp only [outerIntegralForm, mul_sum, map_sum]

end Zeta5Irr
