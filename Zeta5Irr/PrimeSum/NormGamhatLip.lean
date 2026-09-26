/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.NormGamhatShift
public import Mathlib.Algebra.Order.Star.Real

/-!
# A Lipschitz bound for `Γ̂(x, σ)` in `σ`

For `3 ≤ x ≤ M` and `σ, σ' ∈ [1, 2M]`, the two-variable inner functional satisfies
`|Γ̂(x, σ) - Γ̂(x, σ')| ≤ 12 M |σ - σ'|`.

## Main results

* `Zeta5Irr.abs_fract_comp_sub_le`: if `h` is `L`-Lipschitz on `[0, 1]` with `h 0 = h 1`, then
  `|h {a} - h {b}| ≤ L |a - b|` for all real `a, b`.
* `Zeta5Irr.abs_innerLimitingGammaHat_sub_le`: `|Γ̂(x, σ) - Γ̂(x, σ')| ≤ 12 M |σ - σ'|`.

## Implementation notes

* The source proves the bound by splitting `[σ, σ']` at the points `k/2` and `k/2 + ñ(x)`, on
  each of which `Γ̂(x, ·)` is affine with slope at most `12 M`. Here we use instead the
  decomposition `Γ̂(x, σ) = F(2σ) + h({2σ})` of `Zeta5Irr.innerLimitingGammaHat_eq_add_fract`:
  the quadratic `F(2σ)` changes by `2 (σ - σ') (σ + σ' - x - 5/2)`, at most `8 M |σ - σ'|`,
  and `h` is `3/2`-Lipschitz on `[0, 1]` with `h 0 = h 1 = 0`, so `h({2σ})` changes by at most
  `3 |σ - σ'|`.
* The source takes `M ≥ 40` an integer. The bound holds for every real `M ≥ x`, which is the
  form proved here; the hypothesis `M ≥ 40` is not needed.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

/-- If `h` is `L`-Lipschitz on `[0, 1]` and `h 0 = h 1`, then `h ∘ Int.fract` is `L`-Lipschitz
on `ℝ`. -/
theorem abs_fract_comp_sub_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hh : ∀ f ∈ Set.Icc (0 : ℝ) 1, ∀ g ∈ Set.Icc (0 : ℝ) 1, |h f - h g| ≤ L * |f - g|)
    (h01 : h 0 = h 1) (a b : ℝ) :
    |h (Int.fract a) - h (Int.fract b)| ≤ L * |a - b| := by
  have key : ∀ a b : ℝ, a ≤ b → |h (Int.fract a) - h (Int.fract b)| ≤ L * (b - a) := by
    intro a b hab
    have hb0 := Int.fract_nonneg b
    have hA : Int.fract a ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩
    have hB : Int.fract b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb0, (Int.fract_lt_one b).le⟩
    have hfa := Int.floor_add_fract a
    have hfb := Int.floor_add_fract b
    rcases eq_or_lt_of_le (Int.floor_mono hab) with he | hlt
    · have : Int.fract b - Int.fract a = b - a := by
        rw [Int.fract, Int.fract, he]
        ring
      calc |h (Int.fract a) - h (Int.fract b)| ≤ L * |Int.fract a - Int.fract b| :=
            hh _ hA _ hB
        _ = L * (b - a) := by rw [abs_sub_comm, abs_of_nonneg (by linarith), this]
    · have hle : ((⌊a⌋ : ℤ) : ℝ) + 1 ≤ ⌊b⌋ := by exact_mod_cast hlt
      have h1 := hh _ hA 1 ⟨zero_le_one, le_rfl⟩
      have h2 := hh 0 ⟨le_rfl, zero_le_one⟩ _ hB
      rw [abs_of_nonpos (sub_nonpos.2 hA.2), neg_sub] at h1
      rw [zero_sub, abs_neg, abs_of_nonneg hb0] at h2
      calc |h (Int.fract a) - h (Int.fract b)|
          = |(h (Int.fract a) - h 1) + (h 0 - h (Int.fract b))| := by
            rw [h01]
            ring_nf
        _ ≤ |h (Int.fract a) - h 1| + |h 0 - h (Int.fract b)| := abs_add_le _ _
        _ ≤ L * (1 - Int.fract a) + L * Int.fract b := add_le_add h1 h2
        _ ≤ L * (b - a) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (by linarith) hL
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (sub_nonpos.2 hab), neg_sub]
    exact key a b hab
  · rw [abs_of_nonneg (sub_nonneg.2 hab), abs_sub_comm]
    exact key b a hab

/-- A Lipschitz bound for `Γ̂(x, ·)`: for `3 ≤ x ≤ M` and `σ, σ' ∈ [1, 2M]`,
`|Γ̂(x, σ) - Γ̂(x, σ')| ≤ 12 M |σ - σ'|`. The source also assumes `M ≥ 40` an integer. -/
@[zeta5irr "lem_norm_Gamhat_lip"]
theorem abs_innerLimitingGammaHat_sub_le {M x σ σ' : ℝ} (hx : 3 ≤ x) (hxM : x ≤ M)
    (hσ : σ ∈ Set.Icc 1 (2 * M)) (hσ' : σ' ∈ Set.Icc 1 (2 * M)) :
    |innerLimitingGammaHat x σ - innerLimitingGammaHat x σ'| ≤ 12 * M * |σ - σ'| := by
  set n := baseHalfFract x
  have hn0 : 0 ≤ n := baseHalfFract_nonneg x
  have hn1 : n < 1 / 2 := baseHalfFract_lt_half x
  have hqn : basePoleCount x / 2 + n = x := by
    simp only [n, baseHalfFract_def]
    ring
  set h : ℝ → ℝ := fun f => f * n - f ^ 2 / 2 + (f / 2 - n)⁺ with hh_def
  have hLip : ∀ f ∈ Set.Icc (0 : ℝ) 1, ∀ g ∈ Set.Icc (0 : ℝ) 1,
      |h f - h g| ≤ 3 / 2 * |f - g| := by
    rintro f ⟨hf0, hf1⟩ g ⟨hg0, hg1⟩
    have hpos : |(f / 2 - n)⁺ - (g / 2 - n)⁺| ≤ |f - g| / 2 := by
      rw [posPart_def, posPart_def]
      refine (abs_sup_sub_sup_le_abs _ _ _).trans (le_of_eq ?_)
      rw [show f / 2 - n - (g / 2 - n) = (f - g) / 2 by ring, abs_div, abs_two]
    have hlin : |(f - g) * (n - (f + g) / 2)| ≤ |f - g| := by
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩)
    calc |h f - h g| = |(f - g) * (n - (f + g) / 2) +
          ((f / 2 - n)⁺ - (g / 2 - n)⁺)| := by
            simp only [h]
            ring_nf
      _ ≤ |(f - g) * (n - (f + g) / 2)| + |(f / 2 - n)⁺ - (g / 2 - n)⁺| := abs_add_le _ _
      _ ≤ 3 / 2 * |f - g| := by linarith
  have h01 : h 0 = h 1 := by
    simp only [h, posPart_eq_zero.2 (by linarith : (0 : ℝ) / 2 - n ≤ 0),
      posPart_eq_self.2 (by linarith : (0 : ℝ) ≤ 1 / 2 - n)]
    ring
  have hfr := abs_fract_comp_sub_le (by norm_num) hLip h01 (2 * σ) (2 * σ')
  rw [innerLimitingGammaHat_eq_add_fract, innerLimitingGammaHat_eq_add_fract, hqn]
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h1', h2'⟩ := hσ'
  have hquad : |(2 * σ) ^ 2 / 2 - 2 * σ * (x + 5 / 2) - ((2 * σ') ^ 2 / 2 -
      2 * σ' * (x + 5 / 2))| ≤ 8 * M * |σ - σ'| := by
    rw [show (2 * σ) ^ 2 / 2 - 2 * σ * (x + 5 / 2) - ((2 * σ') ^ 2 / 2 -
      2 * σ' * (x + 5 / 2)) = 2 * (σ + σ' - x - 5 / 2) * (σ - σ') by ring, abs_mul, abs_mul,
      abs_two]
    have : |σ + σ' - x - 5 / 2| ≤ 4 * M := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (σ - σ')]
  rw [show 2 * σ - 2 * σ' = 2 * (σ - σ') by ring, abs_mul, abs_two] at hfr
  calc _ = |((2 * σ) ^ 2 / 2 - 2 * σ * (x + 5 / 2) - ((2 * σ') ^ 2 / 2 -
        2 * σ' * (x + 5 / 2))) + (h (Int.fract (2 * σ)) - h (Int.fract (2 * σ')))| := by
          simp only [h, n]
          ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 8 * M * |σ - σ'| + 3 / 2 * (2 * |σ - σ'|) := add_le_add hquad hfr
    _ ≤ 12 * M * |σ - σ'| := by nlinarith [abs_nonneg (σ - σ')]

end Zeta5Irr
