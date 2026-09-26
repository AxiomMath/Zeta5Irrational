/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InBa
public import Zeta5Irr.LocalEstimates.Za
public import Zeta5Irr.LocalEstimates.InEpsCount
public import Zeta5Irr.LocalEstimates.InEpsOrder
public import Zeta5Irr.PrimeSum.NormExtracount
public import Zeta5Irr.PrimeSum.NormEllStep
public import Zeta5Irr.PrimeSum.NormEllAScale
public import Mathlib.Data.Finset.Slice

/-!
# The extras contribute a closed expression

Let `p ≥ 3`, `K = 40 n`, and let `T`, `E`, `ε_a`, `Z_a = T + ε_a`, `b_a` be the common class
dimension, the number of extras, the extras indicator, the class dimension and the inner class
order of the inner range. Then
`∑_{a=1}^{m°} [(Z_a - b_a)(Z_a + b_a - ℓ_K(a) - 5) - (T - b_a)(T + b_a - ℓ_K(a) - 5)]`
equals `E (2T - q̃(K/p) - 5) + E - min(E, 𝒜_p(K))`.

For a class with `ε_a = 0` the bracket vanishes, and for a class with `ε_a = 1` it equals
`2T - ℓ_K(a) - 4`. For `1 ≤ a ≤ m°`, `ℓ_K(a)` is `⌊2K/p⌋ = q̃(K/p)` or `⌊2K/p⌋ + 1`, the latter
exactly on the `𝒜_p(K)` large classes. Since the extras go to classes of largest `ℓ_K`, exactly
`min(E, 𝒜_p(K))` of the `E` classes with `ε_a = 1` are large, whence the formula.

## Main results

* `Zeta5Irr.ellA_eq_or_eq_add_one`: for `1 ≤ a ≤ m°`, `ℓ_K(a) ∈ {⌊2K/p⌋, ⌊2K/p⌋ + 1}`.
* `Zeta5Irr.card_extraClasses`: exactly `E` classes have `ε_a = 1`.
* `Zeta5Irr.card_extraClasses_inter_largeClasses`: the number of large classes with `ε_a = 1`
  is the minimum of the number of classes with `ε_a = 1` and of `𝒜_p(K)`.
* `Zeta5Irr.sum_classDim_bracket`: the closed expression for the contribution of the extras.

## Implementation notes

* The source works under the hypotheses (4.1): `M ≥ 40`, `K ∈ 40 ℤ_{>0}` with `K ≥ 200 M²`,
  and `p` prime with `K/M < p ≤ K/3`. Only `p ≥ 3` is used (through `0 ≤ E < m°`), so it is
  the only hypothesis; the pole bound is `K = 40 n`, as in the definition of `ε_a`.
* The identity is stated in `ℝ`, since `q̃(K/p)` is real valued.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For `1 ≤ a ≤ m°`, the pole count `ℓ_K(a)` is either `⌊2K/p⌋` or `⌊2K/p⌋ + 1`. -/
theorem ellA_eq_or_eq_add_one {p K a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ mStar p) :
    ellA p K a = 2 * K / p ∨ ellA p K a = 2 * K / p + 1 := by
  have hap : 2 * a < p := by rw [mStar_def] at ha₂; omega
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h := ellA_eq_ell_div (A := K) (a := (a : ℤ)) (by omega) (by exact_mod_cast hap)
  have hz₀ : (0 : ℝ) < ((a : ℤ) : ℝ) / p := by
    have : (0 : ℝ) < a := by exact_mod_cast ha₁
    push_cast; positivity
  have hz₁ : ((a : ℤ) : ℝ) / p < 1 / 2 := by
    have : (2 * a : ℝ) < p := by exact_mod_cast hap
    push_cast; rw [div_lt_iff₀ hp]; linarith
  rw [ell_eq_floor_two_mul_add_indicator _ hz₀ hz₁] at h
  have hq : ⌊2 * ((K : ℝ) / p)⌋ = ((2 * K / p : ℕ) : ℤ) := by
    have h2 : ((⌊2 * ((K : ℝ) / p)⌋ : ℤ) : ℝ) = (((2 * K / p : ℕ) : ℤ) : ℝ) := by
      rw [← basePoleCount_def, basePoleCount_natCast_div]
      norm_cast
    exact Int.cast_injective h2
  rw [hq] at h
  generalize 2 * K / p = q at h ⊢
  by_cases hm : ((a : ℤ) : ℝ) / p ∈ normUpperSet ((K : ℝ) / p)
  · rw [Set.indicator_of_mem hm, Pi.one_apply] at h
    right; omega
  · rw [Set.indicator_of_notMem hm] at h
    left; omega

/-- The classes `1 ≤ a ≤ m°` receiving an extra, `ε_a = 1`. -/
def extraClasses (n p M : ℕ) : Finset ℕ :=
  {a ∈ Icc 1 (mStar p) | extraIndicator n p M a = 1}

/-- For `p ≥ 3`, there are exactly `E` classes receiving an extra. -/
theorem card_extraClasses (n : ℕ) {p : ℕ} (M : ℕ) (hp : 3 ≤ p) :
    (#(extraClasses n p M) : ℤ) = extraCount n p M := by
  rw [← sum_extraIndicator_eq_extraCount n M hp, extraClasses, card_filter]
  norm_cast
  refine sum_congr rfl fun a _ => ?_
  have := extraIndicator_le_one n p M a
  split_ifs with h <;> omega

/-- Exactly `min(#{a : ε_a = 1}, 𝒜_p(K))` of the classes receiving an extra are large, where
`K = 40 n`. -/
theorem card_extraClasses_inter_largeClasses (n p M : ℕ) :
    #(extraClasses n p M ∩ largeClasses (poleBound n) p) =
      min #(extraClasses n p M) (largeClassCount (poleBound n) p) := by
  rw [largeClassCount_def]
  by_cases h : extraClasses n p M ⊆ largeClasses (poleBound n) p
  · rw [inter_eq_left.2 h, min_eq_left (card_le_card h)]
  · obtain ⟨a, haS, haL⟩ := not_subset.1 h
    simp only [extraClasses, mem_filter, mem_Icc] at haS
    rw [largeClasses_eq_filter_nat] at haL ⊢
    simp only [mem_filter, mem_Icc, not_and] at haL
    have hqa : ellA p (poleBound n) a = 2 * poleBound n / p :=
      (ellA_eq_or_eq_add_one haS.1.1 haS.1.2).resolve_right (haL haS.1)
    have hLS : (Icc 1 (mStar p)).filter
        (fun c : ℕ => ellA p (poleBound n) c = 2 * poleBound n / p + 1) ⊆
        extraClasses n p M := by
      intro c hc
      simp only [mem_filter] at hc
      simp only [extraClasses, mem_filter]
      refine ⟨hc.1, ?_⟩
      by_contra hne
      have h0 : extraIndicator n p M c = 0 := by
        have := extraIndicator_le_one n p M c; omega
      have := ellA_le_of_extraIndicator haS.2 h0
      omega
    rw [inter_eq_right.2 hLS, min_eq_right (card_le_card hLS)]

/-- **The extras contribute a closed expression.** For `p ≥ 3` and `K = 40 n`,
`∑_{a=1}^{m°} [(Z_a - b_a)(Z_a + b_a - ℓ_K(a) - 5) - (T - b_a)(T + b_a - ℓ_K(a) - 5)]
  = E (2T - q̃(K/p) - 5) + E - min(E, 𝒜_p(K))`. -/
@[zeta5irr "lem_norm_extras_exact"]
theorem sum_classDim_bracket (n : ℕ) {p : ℕ} (M : ℕ) (hp : 3 ≤ p) :
    ∑ a ∈ Icc 1 (mStar p),
      (((classDim n p M a : ℝ) - innerClassOrder p (innerDegree n) a) *
          ((classDim n p M a : ℝ) + innerClassOrder p (innerDegree n) a -
            ellA p (poleBound n) a - 5) -
        ((commonClassDim n p M : ℝ) - innerClassOrder p (innerDegree n) a) *
          ((commonClassDim n p M : ℝ) + innerClassOrder p (innerDegree n) a -
            ellA p (poleBound n) a - 5)) =
      extraCount n p M *
          (2 * commonClassDim n p M - basePoleCount ((poleBound n : ℝ) / p) - 5) +
        extraCount n p M - min (extraCount n p M : ℝ) (largeClassCount (poleBound n) p) := by
  set K := poleBound n
  obtain ⟨q, hq⟩ : ∃ q, 2 * K / p = q := ⟨_, rfl⟩
  set S := extraClasses n p M
  set L := largeClasses K p
  have hterm : ∀ a ∈ Icc 1 (mStar p),
      (((classDim n p M a : ℝ) - innerClassOrder p (innerDegree n) a) *
          ((classDim n p M a : ℝ) + innerClassOrder p (innerDegree n) a -
            ellA p K a - 5) -
        ((commonClassDim n p M : ℝ) - innerClassOrder p (innerDegree n) a) *
          ((commonClassDim n p M : ℝ) + innerClassOrder p (innerDegree n) a -
            ellA p K a - 5)) =
        (extraIndicator n p M a : ℝ) * (2 * commonClassDim n p M - q - 4) -
          if a ∈ S ∩ L then 1 else 0 := by
    intro a ha
    have ha' := mem_Icc.1 ha
    have hS : a ∈ S ↔ extraIndicator n p M a = 1 := by
      simp [S, extraClasses, ha]
    have hL : a ∈ L ↔ ellA p K a = q + 1 := by
      simp [L, largeClasses_eq_filter_nat, ha, hq]
    rw [classDim_def]
    have hε := extraIndicator_le_one n p M a
    rcases hq ▸ ellA_eq_or_eq_add_one (K := K) ha'.1 ha'.2 with hℓ | hℓ <;>
      obtain hε | hε : extraIndicator n p M a = 0 ∨ extraIndicator n p M a = 1 := (by omega) <;>
      simp [mem_inter, hS, hL, hℓ, hε] <;> ring
  have hSL : Icc 1 (mStar p) ∩ (S ∩ L) = S ∩ L :=
    inter_eq_right.2 (inter_subset_left.trans (filter_subset _ _))
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul, sum_ite_mem, sum_const, hSL,
    card_extraClasses_inter_largeClasses, basePoleCount_natCast_div, hq]
  have hE : (∑ a ∈ Icc 1 (mStar p), (extraIndicator n p M a : ℝ)) = extraCount n p M := by
    have := sum_extraIndicator_eq_extraCount n M hp
    exact_mod_cast this
  have hS : (#S : ℝ) = extraCount n p M := by exact_mod_cast card_extraClasses n M hp
  rw [hE, nsmul_eq_mul, mul_one, Nat.cast_min, hS]
  ring

end Zeta5Irr
