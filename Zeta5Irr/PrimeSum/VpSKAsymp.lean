/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Ncal
public import Zeta5Irr.PrimeSum.NormJSum
public import Zeta5Irr.PrimeSum.NormVpSKOuter
public import Mathlib.Algebra.Order.Star.Real

/-!
# The inner asymptotics of `v_p(S_K)`

For a prime `p` in the inner range `K / M < p ≤ K / 3`, the `p`-adic valuation of the scaling
factor `S_K` is `p 𝒩(K/p)` up to an error of at most `2M`, where `𝒩` is the scalar limiting
function.

Since `p² > 2K > 2h`, Legendre's formula reduces to its first term, and `p` is odd, so
`v_p(S_K) = 2h ⌊K/p⌋ - 12h ⌊N/p⌋ - 2 ∑_{i=1}^{h-1} ⌊2i/p⌋`. Writing `x = K/p`, one has
`h = λ p x`, `⌊K/p⌋ = ⌊x⌋` and `⌊N/p⌋ = ⌊α x⌋`, so the first two terms are
`p (2 λ x ⌊x⌋ - 12 λ x ⌊α x⌋)`, and
`v_p(S_K) - p 𝒩(x) = -2 (∑_{i=1}^{h-1} ⌊2i/p⌋ - p 𝒥(h/p))`, which is at most `2M` in
absolute value.

## Main results

* `Zeta5Irr.padicValRat_scalingFactor_sub_mul_scalarLimitingFunction`: for an odd prime `p` with
  `2K < p²`, `v_p(S_K) - p 𝒩(K/p) = -2 (∑_{i=1}^{h-1} ⌊2i/p⌋ - p 𝒥(h/p))`.
* `Zeta5Irr.abs_padicValRat_scalingFactor_sub_mul_scalarLimitingFunction_le`: the estimate
  `|v_p(S_K) - p 𝒩(K/p)| ≤ 2M` for an odd prime `p` with `2K < p²` and `K / M < p`.
* `Zeta5Irr.abs_padicValRat_scalingFactor_sub_mul_scalarLimitingFunction_le_of_le`: the
  source's statement, for integers `M ≥ 40`, `K ≥ 200 M²` and primes `p > K / M`.

## Implementation notes

* The source assumes `M ≥ 40`, `K ≥ 200 M²` and `K / M < p ≤ K / 3`. The argument only uses
  that `p` is an odd prime with `2K < p²` and `K / M < p` for some real `M > 0`; the source's
  hypotheses imply these, since `p > K / M ≥ 200 M ≥ 8000` and `p² > K² / M² ≥ 200 K`. The
  upper bound `p ≤ K / 3` is not used, and is dropped from the source-form statement.
* Since `K = 40 n` is a multiple of `40`, the condition `K ∈ 40 ℤ_{>0}` is the hypothesis
  `0 < n` on the index of the construction; it follows from `K ≥ 200 M²`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.3 (The inner asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- For an odd prime `p` with `2K < p²`,
`v_p(S_K) - p 𝒩(K/p) = -2 (∑_{i=1}^{h-1} ⌊2i/p⌋ - p 𝒥(h/p))`. -/
theorem padicValRat_scalingFactor_sub_mul_scalarLimitingFunction {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : 2 * poleBound n < p ^ 2) :
    (padicValRat p (scalingFactor n) : ℝ) - p * scalarLimitingFunction ((poleBound n : ℝ) / p) =
      -2 * (∑ i ∈ Icc 1 (matrixOrder n - 1), (⌊(2 * i : ℝ) / p⌋ : ℝ) -
        p * innerLimitingFunction ((matrixOrder n : ℝ) / p)) := by
  have := Fact.mk hp
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hfl : ∀ m : ℕ, ⌊(m : ℝ) / p⌋ = ((m / p : ℕ) : ℤ) := fun m => by
    rw [Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  have hα : (innerRatio : ℝ) * ((poleBound n : ℝ) / p) = (innerDegree n : ℝ) / p := by
    simp only [innerRatio, poleBound, innerDegree]; push_cast; ring
  have hlam : (orderRatio : ℝ) * ((poleBound n : ℝ) / p) = (matrixOrder n : ℝ) / p := by
    simp only [orderRatio, poleBound, matrixOrder]; push_cast; ring
  have hi : ∀ i : ℕ, (⌊(2 * i : ℝ) / p⌋ : ℝ) = ((2 * i / p : ℕ) : ℝ) := fun i => by
    rw [show (2 * i : ℝ) = ((2 * i : ℕ) : ℝ) by push_cast; ring, hfl]
    rfl
  have hlamp : (p : ℝ) * ((orderRatio : ℝ) * ((poleBound n : ℝ) / p)) = matrixOrder n := by
    rw [hlam]; field_simp
  have hsum : ∑ i ∈ Icc 1 (matrixOrder n - 1), (⌊(2 * i : ℝ) / p⌋ : ℝ) =
      ((∑ i ∈ Icc 1 (matrixOrder n - 1), (2 * i / p : ℕ) : ℕ) : ℝ) := by
    push_cast [hi]; rfl
  have hv := padicValRat_scalingFactor_of_sq_gt hp2 hK
  have hv' : (padicValRat p (scalingFactor n) : ℝ) =
      2 * matrixOrder n * ((poleBound n / p : ℕ) : ℝ) -
        12 * matrixOrder n * ((innerDegree n / p : ℕ) : ℝ) -
        2 * ((∑ i ∈ Icc 1 (matrixOrder n - 1), (2 * i / p : ℕ) : ℕ) : ℝ) := by
    rw [hv]; simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [hv', hsum, scalarLimitingFunction_def, hα, hlam, hfl, hfl]
  simp only [Int.cast_natCast]
  rw [← hlam]
  generalize ((∑ i ∈ Icc 1 (matrixOrder n - 1), (2 * i / p : ℕ) : ℕ) : ℝ) = S at *
  generalize ((poleBound n / p : ℕ) : ℝ) = a
  generalize ((innerDegree n / p : ℕ) : ℝ) = b
  rw [← hlamp]
  ring

/-- **The inner asymptotics, general form.** For an odd prime `p` with `2K < p²` and a real
`M > 0` with `K / M < p`, `|v_p(S_K) - p 𝒩(K/p)| ≤ 2M`. -/
theorem abs_padicValRat_scalingFactor_sub_mul_scalarLimitingFunction_le {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : 2 * poleBound n < p ^ 2) {M : ℝ} (hM : 0 < M)
    (hpK : (poleBound n : ℝ) / M < p) :
    |(padicValRat p (scalingFactor n) : ℝ) - p * scalarLimitingFunction ((poleBound n : ℝ) / p)|
      ≤ 2 * M := by
  rw [padicValRat_scalingFactor_sub_mul_scalarLimitingFunction hp hp2 hK, abs_mul]
  have := abs_sum_floor_two_mul_div_sub_mul_innerLimitingFunction_le_of_lt hM hpK
  norm_num
  linarith

/-- **Lemma (the inner asymptotics).** For every integer `M ≥ 40`, every `K = 40 n` with
`K ≥ 200 M²` and every prime `p` with `K / M < p`, `|v_p(S_K) - p 𝒩(K/p)| ≤ 2M`.
The source also assumes `p ≤ K / 3`, which is not needed. -/
@[zeta5irr "lem_vpSK_asymp"]
theorem abs_padicValRat_scalingFactor_sub_mul_scalarLimitingFunction_le_of_le {n p M : ℕ}
    (hp : p.Prime) (hM : 40 ≤ M) (hKM : 200 * M ^ 2 ≤ poleBound n)
    (hpK : (poleBound n : ℝ) / M < p) :
    |(padicValRat p (scalingFactor n) : ℝ) - p * scalarLimitingFunction ((poleBound n : ℝ) / p)|
      ≤ 2 * M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hKM' : (200 * M ^ 2 : ℝ) ≤ poleBound n := by exact_mod_cast hKM
  have hpK' : (poleBound n : ℝ) < p * M := (div_lt_iff₀ hM0).1 hpK
  have hM40 : (40 : ℝ) ≤ M := by exact_mod_cast hM
  -- `p > 200 M ≥ 8000`
  have hp200 : (200 * M : ℝ) < p := by nlinarith
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hp200
    linarith
  -- `p² > 200 K > 2 K`
  have hK : 2 * poleBound n < p ^ 2 := by
    have : (2 * poleBound n : ℝ) < p ^ 2 := by nlinarith
    exact_mod_cast this
  exact abs_padicValRat_scalingFactor_sub_mul_scalarLimitingFunction_le hp hp2 hK hM0 hpK

end Zeta5Irr
