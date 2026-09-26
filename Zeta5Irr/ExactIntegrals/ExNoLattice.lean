/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.ExactIntegrals.ExBreaks
public import Zeta5Irr.PrimeSum.NormPwc
public import Mathlib.Algebra.Order.Star.Real

/-!
# No lattice point between consecutive breakpoints

Let `t₀ < t₁ < ⋯` be the increasing enumeration of the breakpoint set `𝓔` of the partition
of `[3, 20]`. For each of the seven slopes `γ ∈ {2, 2α, 2λ, 2H, 4α, 2(1 - α), 2(1 + α)}` and
each `x` with `tᵢ < x < tᵢ₊₁`, the number `γ x` is not an integer. Indeed `3 < x < 20` and
`γ > 0`, so if `γ x = k ∈ ℤ` then `3γ < k < 20γ` and `x = k / γ` is itself a breakpoint,
which cannot lie strictly between two consecutive ones.

## Main results

* `Zeta5Irr.mul_ne_intCast_of_mem_Ioo_exBreaks`: if `tᵢ < x < tᵢ₊₁` and `γ` is one of the
  seven slopes, then `γ x ∉ ℤ`.

## Implementation notes

* The increasing enumeration `i ↦ tᵢ` of `𝓔` is `Finset.orderEmbOfFin`. The point `x` is
  real, as it is in the integrals where the lemma is used; the breakpoints and slopes are
  rational and are cast to `ℝ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.3 (The inner integral).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- Let `t₀ < t₁ < ⋯` enumerate the breakpoint set `𝓔`, and let `γ` be one of the seven
slopes `2, 2α, 2λ, 2H, 4α, 2(1 - α), 2(1 + α)`. If `tᵢ < x < tᵢ₊₁`, then `γ x` is not an
integer. -/
@[zeta5irr "lem_ex_no_lattice"]
theorem mul_ne_intCast_of_mem_Ioo_exBreaks {i : ℕ} (hi : i + 1 < exBreaks.card) {γ : ℚ}
    (hγ : γ ∈ breakSlopes) {x : ℝ}
    (h₁ : (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) < x)
    (h₂ : x < (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)) (k : ℤ) :
    (γ : ℝ) * x ≠ k := by
  intro hk
  have hγ0 : (0 : ℝ) < γ := by exact_mod_cast breakSlopes_pos hγ
  have h3 : (3 : ℝ) ≤ (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) := by
    exact_mod_cast (mem_Icc_of_mem_exBreaks (orderEmbOfFin_mem _ _ _)).1
  have h20 : (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ) ≤ 20 := by
    exact_mod_cast (mem_Icc_of_mem_exBreaks (orderEmbOfFin_mem _ _ _)).2
  have hx : x = ((k / γ : ℚ) : ℝ) := by
    push_cast
    field_simp
    linarith
  have hmem : (k / γ : ℚ) ∈ exBreaks := by
    refine mem_breakpoints.2 (Or.inr (Or.inr ⟨γ, hγ, k, ?_, ?_, rfl⟩))
    · have : (3 * γ : ℝ) < k := by nlinarith
      exact_mod_cast this
    · have : (k : ℝ) < 20 * γ := by nlinarith
      exact_mod_cast this
  rw [hx] at h₁ h₂
  exact notMem_Ioo_orderEmbOfFin rfl hi hmem ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

end Zeta5Irr
