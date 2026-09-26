/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Ncal
public import Zeta5Irr.ExactIntegrals.ExNoLattice
public import Zeta5Irr.ExactIntegrals.FloorConst
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The scalar limiting function is affine between consecutive breakpoints

Let `t₀ < t₁ < ⋯` be the increasing enumeration of the breakpoint set `𝓔` of `[3, 20]`.
On each open interval `(tᵢ, tᵢ₊₁)` the scalar limiting function
`𝒩(x) = 2 λ x ⌊x⌋ - 12 λ x ⌊α x⌋ - 2 𝒥(λ x)` is an affine function `a x + b` with rational
coefficients `a` and `b`.

The three floors `⌊x⌋`, `⌊α x⌋` and `⌊2 λ x⌋` occurring in `𝒩` are constant on
`(tᵢ, tᵢ₊₁)`: none of `x`, `α x`, `2 λ x` is an integer there, since otherwise `2 x`, `2 α x`
or `2 λ x` would be, which no lattice point between breakpoints allows. If their values are
`n₁`, `n₂` and `m`, then
`𝒩(x) = (2 λ n₁ - 12 λ n₂ - 2 m λ) x + m (m + 1) / 2`.

## Main results

* `Zeta5Irr.exists_rat_scalarLimitingFunction_eq_of_mem_Ioo_exBreaks`: for `i + 1 < #𝓔`
  there are `a b : ℚ` with `𝒩(x) = a x + b` whenever `tᵢ < x < tᵢ₊₁`.

## Implementation notes

* The increasing enumeration `i ↦ tᵢ` of `𝓔` is `Finset.orderEmbOfFin`, and the index is a
  natural number `i` with `i + 1 < #𝓔`, as in the source's `0 ≤ i < #𝓔 - 1`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.3 (The inner integral).
-/

@[expose] public section

namespace Zeta5Irr

open Finset Set

/-- Let `t₀ < t₁ < ⋯` enumerate the breakpoint set `𝓔`. For every `i` with `i + 1 < #𝓔`
there are rationals `a` and `b` with `𝒩(x) = a x + b` for every `x` with `tᵢ < x < tᵢ₊₁`. -/
@[zeta5irr "lem_ex_Ncal_affine"]
theorem exists_rat_scalarLimitingFunction_eq_of_mem_Ioo_exBreaks {i : ℕ}
    (hi : i + 1 < exBreaks.card) :
    ∃ a b : ℚ, ∀ x : ℝ, (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) < x →
      x < (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ) →
        scalarLimitingFunction x = a * x + b := by
  set l : ℝ := (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ)
  set r : ℝ := (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)
  have hlat : ∀ γ ∈ breakSlopes, ∀ y ∈ Ioo l r, ∀ k : ℤ, (γ : ℝ) * y ≠ k :=
    fun γ hγ y hy k => mul_ne_intCast_of_mem_Ioo_exBreaks hi hγ hy.1 hy.2 k
  have h1 : ∀ y ∈ Ioo l r, ∀ k : ℤ, (1 : ℝ) * y ≠ k := by
    intro y hy k hk
    refine hlat 2 (by simp [breakSlopes]) y hy (2 * k) ?_
    push_cast
    linarith
  have h2 : ∀ y ∈ Ioo l r, ∀ k : ℤ, (innerRatio : ℝ) * y ≠ k := by
    intro y hy k hk
    refine hlat (2 * innerRatio) (by simp [breakSlopes]) y hy (2 * k) ?_
    push_cast
    linarith
  have h3 : ∀ y ∈ Ioo l r, ∀ k : ℤ, ((2 * orderRatio : ℚ) : ℝ) * y ≠ k :=
    hlat _ (by simp [breakSlopes])
  have hlr : l < r := by
    simp only [l, r, Rat.cast_lt, OrderEmbedding.lt_iff_lt, Fin.mk_lt_mk]
    omega
  set x₀ : ℝ := (l + r) / 2
  have hx₀ : x₀ ∈ Ioo l r := ⟨by simp only [x₀]; linarith, by simp only [x₀]; linarith⟩
  set n₁ : ℤ := ⌊x₀⌋
  set n₂ : ℤ := ⌊(innerRatio : ℝ) * x₀⌋
  set m : ℤ := ⌊((2 * orderRatio : ℚ) : ℝ) * x₀⌋
  refine ⟨2 * orderRatio * n₁ - 12 * orderRatio * n₂ - 2 * m * orderRatio, m * (m + 1) / 2,
    fun x hl hr => ?_⟩
  have hx : x ∈ Ioo l r := ⟨hl, hr⟩
  have e1 : ⌊x⌋ = n₁ := by
    simpa using floor_mul_eq_floor_mul_of_mem_Ioo h1 hx hx₀
  have e2 : ⌊(innerRatio : ℝ) * x⌋ = n₂ := floor_mul_eq_floor_mul_of_mem_Ioo h2 hx hx₀
  have e3 : ⌊2 * ((orderRatio : ℝ) * x)⌋ = m := by
    rw [show (2 : ℝ) * ((orderRatio : ℝ) * x) = ((2 * orderRatio : ℚ) : ℝ) * x by
      push_cast; ring]
    exact floor_mul_eq_floor_mul_of_mem_Ioo h3 hx hx₀
  rw [scalarLimitingFunction_of_floor_eq e1 e2 e3]
  push_cast
  ring

end Zeta5Irr
