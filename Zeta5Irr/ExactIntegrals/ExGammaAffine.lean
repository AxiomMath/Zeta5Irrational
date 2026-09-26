/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Gamma
public import Zeta5Irr.ExactIntegrals.ExMeanZero
public import Zeta5Irr.ExactIntegrals.ExB1
public import Zeta5Irr.ExactIntegrals.ExB1Mixed
public import Zeta5Irr.ExactIntegrals.ExNoLattice
public import Zeta5Irr.ExactIntegrals.FloorConst

/-!
# The inner limiting function is affine between consecutive breakpoints

Let `t₀ < t₁ < ⋯` be the increasing enumeration of the breakpoint set `𝓔` of `[3, 20]`.
On each open interval `(tᵢ, tᵢ₊₁)` the inner limiting function `Γ` is an affine function
`a x + b` with rational coefficients `a` and `b`.

The proof has three steps. First, writing `ℓ(x, z) = Ψ_x(z) + 2 x` and
`b(x, z) = 3 Ψ_{α x}(z) + 6 α x`, the integrand of `Γ` expands into a constant, terms linear
in `Ψ_x` and `Ψ_{α x}`, and the quadratic terms `Ψ_{α x}²` and `Ψ_x Ψ_{α x}`. The linear terms
integrate to `0` and the quadratic ones are evaluated in terms of `f = x - ⌊x⌋`,
`g = α x - ⌊α x⌋`, `d₀` and `e`, which gives a closed form of `Γ` valid for every real `x`.
Second, on `(tᵢ, tᵢ₊₁)` none of the seven numbers `γ x` is an integer, so the floors
`⌊2 H x⌋`, `⌊2 x⌋`, `⌊x⌋`, `⌊α x⌋`, `⌊2 α x⌋` are constant there, as are the signs `e(f)`,
`e(g)`, the choice of the smaller of `d₀(f)`, `d₀(g)`, and the branch of the positive part
`(s̃(x) - ñ(x))₊`; each of these can only switch at an `x` where some `γ x` is an integer.
Hence every summand of the closed form is a polynomial of degree at most `2` in `x`. Third,
the coefficient of `x²` is `18 α² (e(g)² - 1) - 6 α (e(f)² e(g)² - 1) = 0`.

## Main results

* `Zeta5Irr.innerLimitingGamma_eq`: the closed form of `Γ`,
  `Γ(x) = P S / 2 - 9 d₀(g) (1 - 2 d₀(g)) + 3 e(f) e(g) (min(d₀(f), d₀(g)) - 2 d₀(f) d₀(g))`
  `  + s̃(x) (2 T̃(x) - q̃(x) - 5) + (s̃(x) - ñ(x))₊`, where `P = T̃(x) - 6 α x` and
  `S = T̃(x) + 6 α x - 2 x - 5`.
* `Zeta5Irr.exists_rat_innerLimitingGamma_eq_of_mem_Ioo_exBreaks`: for `i + 1 < #𝓔` there
  are `a b : ℚ` with `Γ(x) = a x + b` whenever `tᵢ < x < tᵢ₊₁`.

## Implementation notes

* The increasing enumeration `i ↦ tᵢ` of `𝓔` is `Finset.orderEmbOfFin`, and the index is a
  natural number `i` with `i + 1 < #𝓔`, as in the source's `0 ≤ i < #𝓔 - 1`.
* The sign `e(f)` is identified on the interval with the integer `1 + 4 ⌊x⌋ - 2 ⌊2 x⌋`
  (`Zeta5Irr.esign_fract_eq`), and `d₀(u) = e(u) u + (1 - e(u)) / 2`
  (`Zeta5Irr.d₀_eq_esign_mul_add`); this makes the constancy of the signs a consequence of the
  constancy of the floors. The constancy of the branch of the minimum and of the positive part
  is an intermediate value argument (`Zeta5Irr.forall_lt_or_forall_lt_of_isPreconnected`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §7.3 (The inner integral).
-/

@[expose] public section

namespace Zeta5Irr

open MeasureTheory Set Finset

/-- **The closed form of `Γ`.** Writing `f = x - ⌊x⌋`, `g = α x - ⌊α x⌋`,
`P = T̃(x) - 6 α x` and `S = T̃(x) + 6 α x - 2 x - 5`,
`Γ(x) = P S / 2 - 9 d₀(g) (1 - 2 d₀(g)) + 3 e(f) e(g) (min(d₀(f), d₀(g)) - 2 d₀(f) d₀(g))`
`  + s̃(x) (2 T̃(x) - q̃(x) - 5) + (s̃(x) - ñ(x))₊`. -/
theorem innerLimitingGamma_eq (x : ℝ) :
    innerLimitingGamma x =
      (innerLimit x - 6 * innerRatio * x) * (innerLimit x + 6 * innerRatio * x - 2 * x - 5) / 2 -
        9 * (d₀ (Int.fract (innerRatio * x)) * (1 - 2 * d₀ (Int.fract (innerRatio * x)))) +
        3 * (esign (Int.fract x) * esign (Int.fract (innerRatio * x)) *
          (min (d₀ (Int.fract x)) (d₀ (Int.fract (innerRatio * x))) -
            2 * d₀ (Int.fract x) * d₀ (Int.fract (innerRatio * x)))) +
        allocationRemainder x * (2 * innerLimit x - basePoleCount x - 5) +
        (allocationRemainder x - baseHalfFract x)⁺ := by
  rw [innerLimitingGamma_def, integral_innerIntegrand_eq, integral_psi_sq,
    integral_psi_mul_psi, posPart_def]

/-- If `2 y` is not an integer, then `e(y - ⌊y⌋) = 1 + 4 ⌊y⌋ - 2 ⌊2 y⌋`. -/
theorem esign_fract_eq {y : ℝ} (h : ∀ k : ℤ, 2 * y ≠ k) :
    esign (Int.fract y) = 1 + 4 * ⌊y⌋ - 2 * ⌊2 * y⌋ := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  rw [Int.fract]
  rcases lt_or_gt_of_ne (show y - ⌊y⌋ ≠ 1 / 2 from fun he => h (2 * ⌊y⌋ + 1) (by
    push_cast; linarith)) with hlt | hgt
  · have : ⌊2 * y⌋ = 2 * ⌊y⌋ := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [esign_of_le hlt.le, this]
    push_cast
    ring
  · have : ⌊2 * y⌋ = 2 * ⌊y⌋ + 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [esign_of_lt hgt, this]
    push_cast
    ring

/-- `d₀(u) = e(u) u + (1 - e(u)) / 2`. -/
theorem d₀_eq_esign_mul_add (u : ℝ) : d₀ u = esign u * u + (1 - esign u) / 2 := by
  rw [d₀_def]
  rcases le_or_gt u (1 / 2) with h | h
  · rw [esign_of_le h, min_eq_left (by linarith)]
    ring
  · rw [esign_of_lt h, min_eq_right (by linarith)]
    ring

/-- If `u` and `v` are continuous on a preconnected set `s` and never agree there, then one of
them is strictly smaller than the other throughout `s`. -/
theorem forall_lt_or_forall_lt_of_isPreconnected {s : Set ℝ} {u v : ℝ → ℝ}
    (hs : IsPreconnected s) (hu : ContinuousOn u s) (hv : ContinuousOn v s)
    (hne : ∀ x ∈ s, u x ≠ v x) : (∀ x ∈ s, u x < v x) ∨ (∀ x ∈ s, v x < u x) := by
  by_contra h
  push Not at h
  obtain ⟨⟨a, ha, hua⟩, ⟨b, hb, hvb⟩⟩ := h
  obtain ⟨y, hy, h0⟩ := hs.intermediate_value hb ha (hu.sub hv)
    (show (0 : ℝ) ∈ Icc (u b - v b) (u a - v a) from ⟨by linarith, by linarith⟩)
  exact hne y hy (sub_eq_zero.1 h0)

/-- Let `t₀ < t₁ < ⋯` enumerate the breakpoint set `𝓔`. For every `i` with `i + 1 < #𝓔`
there are rationals `a` and `b` with `Γ(x) = a x + b` for every `x` with `tᵢ < x < tᵢ₊₁`. -/
@[zeta5irr "lem_ex_Gamma_affine"]
theorem exists_rat_innerLimitingGamma_eq_of_mem_Ioo_exBreaks {i : ℕ}
    (hi : i + 1 < exBreaks.card) :
    ∃ a b : ℚ, ∀ x : ℝ, (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ) < x →
      x < (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ) →
        innerLimitingGamma x = a * x + b := by
  set l : ℝ := (exBreaks.orderEmbOfFin rfl ⟨i, by omega⟩ : ℝ)
  set r : ℝ := (exBreaks.orderEmbOfFin rfl ⟨i + 1, hi⟩ : ℝ)
  have hlat : ∀ γ ∈ breakSlopes, ∀ y ∈ Ioo l r, ∀ k : ℤ, (γ : ℝ) * y ≠ k :=
    fun γ hγ y hy k => mul_ne_intCast_of_mem_Ioo_exBreaks hi hγ hy.1 hy.2 k
  have hα : ∀ y ∈ Ioo l r, ∀ k : ℤ, 2 * ((innerRatio : ℝ) * y) ≠ k := fun y hy k hk =>
    hlat (2 * innerRatio) (by simp [breakSlopes]) y hy k (by push_cast; linarith)
  have h2 : ∀ y ∈ Ioo l r, ∀ k : ℤ, 2 * y ≠ k := fun y hy k hk =>
    hlat 2 (by simp [breakSlopes]) y hy k (by push_cast; linarith)
  have h1 : ∀ y ∈ Ioo l r, ∀ k : ℤ, (1 : ℝ) * y ≠ k := fun y hy k hk =>
    h2 y hy (2 * k) (by push_cast; linarith)
  have hα1 : ∀ y ∈ Ioo l r, ∀ k : ℤ, (innerRatio : ℝ) * y ≠ k := fun y hy k hk =>
    hα y hy (2 * k) (by push_cast; linarith)
  have hα2 : ∀ y ∈ Ioo l r, ∀ k : ℤ, (2 * innerRatio : ℝ) * y ≠ k := fun y hy k hk =>
    hα y hy k (by linarith)
  have hH : ∀ y ∈ Ioo l r, ∀ k : ℤ, (2 * heightRatio : ℝ) * y ≠ k := fun y hy k hk =>
    hlat (2 * heightRatio) (by simp [breakSlopes]) y hy k (by push_cast; linarith)
  have hlr : l < r := by
    simp only [l, r, Rat.cast_lt, OrderEmbedding.lt_iff_lt, Fin.mk_lt_mk]
    omega
  set x₀ : ℝ := (l + r) / 2
  have hx₀ : x₀ ∈ Ioo l r := ⟨by simp only [x₀]; linarith, by simp only [x₀]; linarith⟩
  -- the floors are constant on `(l, r)`
  set T : ℤ := ⌊2 * (heightRatio : ℝ) * x₀⌋
  set q : ℤ := ⌊2 * x₀⌋
  set n₁ : ℤ := ⌊x₀⌋
  set n₂ : ℤ := ⌊(innerRatio : ℝ) * x₀⌋
  set n₃ : ℤ := ⌊2 * ((innerRatio : ℝ) * x₀)⌋
  have eT : ∀ x ∈ Ioo l r, ⌊2 * (heightRatio : ℝ) * x⌋ = T := fun x hx =>
    floor_mul_eq_floor_mul_of_mem_Ioo hH hx hx₀
  have eq : ∀ x ∈ Ioo l r, ⌊2 * x⌋ = q := fun x hx =>
    floor_mul_eq_floor_mul_of_mem_Ioo h2 hx hx₀
  have e₁ : ∀ x ∈ Ioo l r, ⌊x⌋ = n₁ := fun x hx => by
    simpa using floor_mul_eq_floor_mul_of_mem_Ioo h1 hx hx₀
  have e₂ : ∀ x ∈ Ioo l r, ⌊(innerRatio : ℝ) * x⌋ = n₂ := fun x hx =>
    floor_mul_eq_floor_mul_of_mem_Ioo hα1 hx hx₀
  have e₃ : ∀ x ∈ Ioo l r, ⌊2 * ((innerRatio : ℝ) * x)⌋ = n₃ := fun x hx => by
    have := floor_mul_eq_floor_mul_of_mem_Ioo hα2 hx hx₀
    rwa [mul_assoc, mul_assoc] at this
  -- the signs are constant on `(l, r)`
  set εf : ℤ := 1 + 4 * n₁ - 2 * q
  set εg : ℤ := 1 + 4 * n₂ - 2 * n₃
  have hef : ∀ x ∈ Ioo l r, esign (Int.fract x) = εf := fun x hx => by
    rw [esign_fract_eq (h2 x hx), e₁ x hx, eq x hx]
    push_cast [εf]
    ring
  have heg : ∀ x ∈ Ioo l r, esign (Int.fract ((innerRatio : ℝ) * x)) = εg := fun x hx => by
    rw [esign_fract_eq (hα x hx), e₂ x hx, e₃ x hx]
    push_cast [εg]
    ring
  have hεf : (εf : ℝ) = 1 ∨ (εf : ℝ) = -1 := hef x₀ hx₀ ▸ esign_eq_one_or_eq_neg_one _
  have hεg : (εg : ℝ) = 1 ∨ (εg : ℝ) = -1 := heg x₀ hx₀ ▸ esign_eq_one_or_eq_neg_one _
  have hεf2 : (εf : ℝ) ^ 2 = 1 := by rcases hεf with h | h <;> rw [h] <;> norm_num
  have hεg2 : (εg : ℝ) ^ 2 = 1 := by rcases hεg with h | h <;> rw [h] <;> norm_num
  -- `d₀(f)` and `d₀(g)` are affine on `(l, r)`
  set Df : ℚ := -(εf * n₁) + (1 - εf) / 2
  set Dg : ℚ := -(εg * n₂) + (1 - εg) / 2
  have hdf : ∀ x ∈ Ioo l r, d₀ (Int.fract x) = εf * x + Df := fun x hx => by
    rw [d₀_eq_esign_mul_add, hef x hx, Int.fract, e₁ x hx]
    push_cast [Df]
    ring
  have hdg : ∀ x ∈ Ioo l r, d₀ (Int.fract ((innerRatio : ℝ) * x)) =
      ((εg * innerRatio : ℚ) : ℝ) * x + Dg := fun x hx => by
    rw [d₀_eq_esign_mul_add, heg x hx, Int.fract, e₂ x hx]
    push_cast [Dg]
    ring
  -- the minimum `min(d₀(f), d₀(g))` is affine on `(l, r)`
  obtain ⟨c₁, c₀, hmin⟩ : ∃ c₁ c₀ : ℚ, ∀ x ∈ Ioo l r,
      min (d₀ (Int.fract x)) (d₀ (Int.fract ((innerRatio : ℝ) * x))) = c₁ * x + c₀ := by
    have hne : ∀ x ∈ Ioo l r, (fun x : ℝ => (εf : ℝ) * x + Df) x ≠
        (fun x : ℝ => ((εg * innerRatio : ℚ) : ℝ) * x + Dg) x := by
      intro x hx he
      simp only [Df, Dg] at he
      push_cast at he
      rcases hεf with hf | hf <;> rcases hεg with hg | hg <;> rw [hf, hg] at he
      · exact hlat (2 * (1 - innerRatio)) (by simp [breakSlopes]) x hx (2 * (n₁ - n₂))
          (by push_cast; linarith)
      · exact hlat (2 * (1 + innerRatio)) (by simp [breakSlopes]) x hx (2 * (n₁ + n₂ + 1))
          (by push_cast; linarith)
      · exact hlat (2 * (1 + innerRatio)) (by simp [breakSlopes]) x hx (2 * (n₁ + n₂ + 1))
          (by push_cast; linarith)
      · exact hlat (2 * (1 - innerRatio)) (by simp [breakSlopes]) x hx (2 * (n₁ - n₂))
          (by push_cast; linarith)
    rcases forall_lt_or_forall_lt_of_isPreconnected isPreconnected_Ioo (by fun_prop)
      (by fun_prop) hne with h | h
    · exact ⟨εf, Df, fun x hx => by
        rw [hdf x hx, hdg x hx, min_eq_left (h x hx).le]; push_cast; ring⟩
    · exact ⟨εg * innerRatio, Dg, fun x hx => by
        rw [hdf x hx, hdg x hx, min_eq_right (h x hx).le]⟩
  -- the positive part `(s̃(x) - ñ(x))₊` is affine on `(l, r)`
  obtain ⟨p₁, p₀, hpos⟩ : ∃ p₁ p₀ : ℚ, ∀ x ∈ Ioo l r,
      (allocationRemainder x - baseHalfFract x)⁺ = p₁ * x + p₀ := by
    have hsn : ∀ x ∈ Ioo l r, allocationRemainder x - baseHalfFract x =
        ((2 * innerRatio : ℚ) : ℝ) * x + ((-(T - q) / 2 : ℚ) : ℝ) := fun x hx => by
      rw [allocationRemainder_def, baseHalfFract_def, innerLimit_def, basePoleCount_def,
        eT x hx, eq x hx]
      push_cast
      norm_num [heightRatio, innerRatio]
      ring
    have hne : ∀ x ∈ Ioo l r,
        (fun x : ℝ => ((2 * innerRatio : ℚ) : ℝ) * x + ((-(T - q) / 2 : ℚ) : ℝ)) x ≠
          (fun _ => (0 : ℝ)) x := by
      intro x hx he
      refine hlat (4 * innerRatio) (by simp [breakSlopes]) x hx (T - q) ?_
      push_cast at he ⊢
      linarith
    rcases forall_lt_or_forall_lt_of_isPreconnected isPreconnected_Ioo (by fun_prop)
      (by fun_prop) hne with h | h
    · exact ⟨0, 0, fun x hx => by
        rw [hsn x hx, posPart_eq_zero.2 (h x hx).le]; simp⟩
    · exact ⟨2 * innerRatio, -(T - q) / 2, fun x hx => by
        rw [hsn x hx, posPart_eq_self.2 (h x hx).le]⟩
  -- collect the closed form; the quadratic terms cancel
  refine ⟨-T + 15 * innerRatio - 9 * εg * innerRatio + 36 * εg * innerRatio * Dg +
      3 * εf * εg * c₁ - 6 * εf * εg * (εf * Dg + εg * innerRatio * Df) +
      heightRatio * (2 * T - q - 5) + p₁,
    T * (T - 5) / 2 - 9 * Dg + 18 * Dg ^ 2 + 3 * εf * εg * c₀ - 6 * εf * εg * Df * Dg -
      T / 2 * (2 * T - q - 5) + p₀, fun x hl hr => ?_⟩
  have hx : x ∈ Ioo l r := ⟨hl, hr⟩
  rw [innerLimitingGamma_eq, hmin x hx, hpos x hx, hdf x hx, hdg x hx, hef x hx, heg x hx,
    allocationRemainder_def, innerLimit_def, eT x hx, basePoleCount_def, eq x hx]
  push_cast
  linear_combination (18 * (innerRatio : ℝ) ^ 2 - 6 * innerRatio) * x ^ 2 * hεg2 -
    6 * (innerRatio : ℝ) * (εg : ℝ) ^ 2 * x ^ 2 * hεf2

end Zeta5Irr
