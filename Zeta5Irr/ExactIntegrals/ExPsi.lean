/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.EllXz

/-!
# The normalized function `Ψ_u(z)`

For real `u` and `z` we set
`Ψ_u(z) = ℓ(u, z) - 2u`,
where `ℓ(u, z) = ⌊u - z⌋ + ⌊u + z⌋ + 1` is the integer-valued function of `Zeta5Irr.ell`.
Subtracting `2u` removes the linear growth of `ℓ` in `u`: the result is `1`-periodic in `u`,
even in `z`, and takes values in `(-1, 1]`. In the source it is integrated in `z` over
`[0, 1/2]`.

## Main definitions

* `Zeta5Irr.psi`: the function `Ψ_u(z) = ℓ(u, z) - 2u`.

## Main results

* `Zeta5Irr.psi_add_intCast`: `Ψ_{u + m}(z) = Ψ_u(z)` for an integer `m`.
* `Zeta5Irr.psi_neg_right`: `Ψ_u(-z) = Ψ_u(z)`.
* `Zeta5Irr.psi_le`, `Zeta5Irr.neg_one_lt_psi`: `-1 < Ψ_u(z) ≤ 1`.
* `Zeta5Irr.intervalIntegrable_psi`, `Zeta5Irr.intervalIntegrable_psi_mul_psi`: `Ψ_u` and
  `Ψ_u Ψ_v` are interval integrable on every interval.

## Implementation notes

* The source states the definition for `0 ≤ z ≤ 1/2`. The formula makes sense for all real
  `u` and `z`, so `Ψ` is a function `ℝ → ℝ → ℝ`, and the constraint on `z` is a hypothesis
  of the results that need it. None of the lemmas in this file need it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.1: fractional parts and the two `z`-integrals.
-/

@[expose] public section

namespace Zeta5Irr

/-- The function `Ψ_u(z) = ℓ(u, z) - 2u`, for all real `u` and `z`. -/
@[zeta5irr "def_ex_psi"]
noncomputable def psi (u z : ℝ) : ℝ := ell u z - 2 * u

/-- `Ψ_u(z) = ℓ(u, z) - 2u`, by definition. -/
theorem psi_def (u z : ℝ) : psi u z = ell u z - 2 * u := rfl

/-- `Ψ` is `1`-periodic in `u`: `Ψ_{u + m}(z) = Ψ_u(z)` for an integer `m`. -/
theorem psi_add_intCast (u z : ℝ) (m : ℤ) : psi (u + m) z = psi u z := by
  rw [psi_def, psi_def, ell_add_intCast]
  push_cast
  ring

/-- `Ψ` is even in `z`: `Ψ_u(-z) = Ψ_u(z)`. -/
theorem psi_neg_right (u z : ℝ) : psi u (-z) = psi u z := by
  rw [psi_def, psi_def, ell_neg_right]

/-- `Ψ_u(0) = 2 ⌊u⌋ + 1 - 2u`. -/
@[simp]
theorem psi_zero_right (u : ℝ) : psi u 0 = 2 * ⌊u⌋ + 1 - 2 * u := by
  simp [psi_def]

/-- `Ψ_u(z) ≤ 1`. -/
theorem psi_le (u z : ℝ) : psi u z ≤ 1 := by
  have := ell_le u z
  rw [psi_def]
  linarith

/-- `-1 < Ψ_u(z)`. -/
theorem neg_one_lt_psi (u z : ℝ) : -1 < psi u z := by
  have := lt_ell u z
  rw [psi_def]
  linarith

/-- `|Ψ_u(z)| ≤ 1`. -/
theorem abs_psi_le (u z : ℝ) : |psi u z| ≤ 1 :=
  abs_le.2 ⟨(neg_one_lt_psi u z).le, psi_le u z⟩

/-- For fixed `u`, `z ↦ Ψ_u(z)` is measurable. -/
theorem measurable_psi (u : ℝ) : Measurable (psi u) := by
  unfold psi ell
  fun_prop

/-- `z ↦ Ψ_u(z)` is interval integrable on every interval. -/
theorem intervalIntegrable_psi (u a b : ℝ) :
    IntervalIntegrable (fun z => psi u z) MeasureTheory.volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
    (measurable_psi u).aestronglyMeasurable (Filter.Eventually.of_forall (abs_psi_le u))

/-- `z ↦ Ψ_u(z) Ψ_v(z)` is interval integrable on every interval. -/
theorem intervalIntegrable_psi_mul_psi (u v a b : ℝ) :
    IntervalIntegrable (fun z => psi u z * psi v z) MeasureTheory.volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
    ((measurable_psi u).mul (measurable_psi v)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul (abs_psi_le u z) (abs_psi_le v z) (abs_nonneg _) zero_le_one

end Zeta5Irr
