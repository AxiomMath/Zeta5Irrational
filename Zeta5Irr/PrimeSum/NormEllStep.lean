/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.EllXz
public import Zeta5Irr.PrimeSum.NormUpperset

/-!
# The step structure of `ℓ(x, z)`

For real `x` and `0 < z < 1/2`, the integer `ℓ(x, z) = ⌊x - z⌋ + ⌊x + z⌋ + 1` equals
`⌊2x⌋ + 𝟙_{S(x)}(z)`, where `S(x)` is the step set: `(0, {x}]` if `{x} < 1/2` and
`[1 - {x}, 1/2)` otherwise. Thus, as a function of `z ∈ (0, 1/2)`, `ℓ(x, z)` takes the value
`⌊2x⌋ + 1` exactly on `S(x)` and `⌊2x⌋` elsewhere.

## Main results

* `Zeta5Irr.ell_eq_floor_two_mul_add_indicator`: `ℓ(x, z) = ⌊2x⌋ + 𝟙_{S(x)}(z)` for
  `0 < z < 1/2`.

## Implementation notes

* The indicator is `Set.indicator (normUpperSet x) 1 z`, valued in `ℤ`.
* The proof writes `x = ⌊x⌋ + {x}` and computes each floor with `Int.floor_eq_iff`, in the
  two cases `{x} < 1/2` and `{x} ≥ 1/2`, each split according to membership of `z` in `S(x)`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.2 (The step structure of the pole counts).
-/

@[expose] public section

namespace Zeta5Irr

/-- For `0 < z < 1/2`, `ℓ(x, z) = ⌊2x⌋ + 𝟙_{S(x)}(z)`. -/
@[zeta5irr "lem_norm_ell_step"]
theorem ell_eq_floor_two_mul_add_indicator (x : ℝ) {z : ℝ} (hz₀ : 0 < z) (hz₁ : z < 1 / 2) :
    ell x z = ⌊2 * x⌋ + (normUpperSet x).indicator 1 z := by
  set n := ⌊x⌋ with hn
  set f := Int.fract x with hf
  have hx : x = n + f := (Int.floor_add_fract x).symm
  have hf₀ : 0 ≤ f := Int.fract_nonneg x
  have hf₁ : f < 1 := Int.fract_lt_one x
  rw [ell_def]
  rcases lt_or_ge f (1 / 2) with h | h
  · have h2 : ⌊2 * x⌋ = 2 * n := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hp : ⌊x + z⌋ = n := by
      rw [Int.floor_eq_iff]; constructor <;> linarith
    rw [normUpperSet_of_lt h, h2, hp]
    by_cases hzf : z ≤ f
    · have hm : ⌊x - z⌋ = n := by
        rw [Int.floor_eq_iff]; constructor <;> linarith
      rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hz₀, hzf⟩), hm]; simp; ring
    · rw [not_le] at hzf
      have hm : ⌊x - z⌋ = n - 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [Set.indicator_of_notMem (fun hm ↦ hzf.not_ge hm.2), hm]; simp; ring
  · have h2 : ⌊2 * x⌋ = 2 * n + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hm : ⌊x - z⌋ = n := by
      rw [Int.floor_eq_iff]; constructor <;> linarith
    rw [normUpperSet_of_le h, h2, hm]
    by_cases hzf : 1 - f ≤ z
    · have hp : ⌊x + z⌋ = n + 1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [Set.indicator_of_mem (Set.mem_Ico.2 ⟨hzf, hz₁⟩), hp]; simp; ring
    · rw [not_le] at hzf
      have hp : ⌊x + z⌋ = n := by
        rw [Int.floor_eq_iff]; constructor <;> linarith
      rw [Set.indicator_of_notMem (fun hm ↦ hzf.not_ge hm.1), hp]; simp; ring

end Zeta5Irr
