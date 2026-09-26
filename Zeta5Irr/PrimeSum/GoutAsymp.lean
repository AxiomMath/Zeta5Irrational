/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.GammaOut
public import Zeta5Irr.PrimeSum.NormGoutFar
public import Zeta5Irr.PrimeSum.NormGoutNear
public import Mathlib.RingTheory.PiTensorProduct

/-!
# The outer exponent asymptotics

Let `K = 40 n`, `N = 3 n = α K` and let `p` satisfy `K / 3 < p ≤ K`; put `y = p / K`. Then the
outer exponent `γ_p^out` is, up to a bounded error, `-K (R₀(y) - d_rk(y))`:
```
|-γ_p^out - K (R₀(p/K) - d_rk(p/K))| ≤ 20.
```
In the far case `K < 2 p` one has `K mod p = K - p`, and in the near case `2 p ≤ K` one has
`K mod p = K - 2 p`. In either case every quantity entering `γ_p^out` (the overlap count `u`,
the small-class count `t_p` and the rank bound `r_p`) is, up to an additive error of at most
`2`, `K` times the corresponding piecewise-linear function of `y`, because `max` and `min` are
`1`-Lipschitz in each argument. The limiting expressions are identified with `R₀(y)` and
`R₀(y) - d_rk(y)` by the two normalisation identities of §8.4; the errors add up to at most
`9` in the far case and `10` in the near case.

## Main results

* `Zeta5Irr.abs_neg_outerExponent_sub_le`: the bound above.

## Implementation notes

The source states the bound for every integer `M ≥ 40`, every `K ∈ 40 ℤ_{>0}` with
`K ≥ 200 M²` and every prime `p` with `K/3 < p ≤ K`. The parameter `M` does not occur in the
conclusion, and neither the size condition `K ≥ 200 M²` nor the primality of `p` is used in
the proof, so the statement here is for `K = 40 n` with `n` arbitrary and any natural number
`p` with `K < 3 p` and `p ≤ K` (which forces `n > 0`).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.4 (The outer asymptotics).
-/

@[expose] public section

namespace Zeta5Irr

/-- Clipping the first argument below at `0` on the left and the second on the right does not
increase their distance. -/
theorem abs_max_zero_sub_max_zero_le (a b : ℝ) : |max 0 a - max b 0| ≤ |a - b| := by
  rw [max_comm 0 a]
  exact abs_max_sub_max_le_abs a b 0

/-- The far case `K < 2 p` of the outer exponent asymptotics, with error at most `9`. -/
theorem abs_neg_outerExponent_sub_le_of_lt {n p : ℕ} (hp₂ : p ≤ poleBound n)
    (hlt : poleBound n < 2 * p) :
    |-(outerExponent p (innerDegree n) (poleBound n) : ℝ) -
        poleBound n * (outerLimitingFunction (p / poleBound n) -
          rankDefect (p / poleBound n))| ≤ 9 := by
  set K := poleBound n with hKdef
  set N := innerDegree n with hNdef
  have hKN : (K : ℝ) = 40 * n := by simp [hKdef, poleBound]
  have hNN : (N : ℝ) = 3 * n := by simp [hNdef, innerDegree]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  set y : ℝ := p / K with hy
  have hKy : (K : ℝ) * y = p := by
    rw [hy]
    field_simp
  have hc : ∀ c : ℝ, (K : ℝ) * (c * y) = c * p := fun c => by rw [← hKy]; ring
  have e2 : (K : ℝ) * (3 / 40) = N := by
    rw [hKN, hNN]
    ring
  have e3 : (K : ℝ) * (4 * (3 / 40)) = 4 * N := by
    rw [hKN, hNN]
    ring
  have hy₂ : y ≤ 1 := by
    rw [hy, div_le_one hK0]
    exact_mod_cast hp₂
  have hy₃ : 1 / 2 < y := by
    have : (K : ℝ) < 2 * p := by exact_mod_cast hlt
    rw [hy, lt_div_iff₀ hK0]
    linarith
  have hvz : (vA p K : ℤ) = K - p := by
    rw [vA, Nat.mod_eq_sub_mod hp₂, Nat.mod_eq_of_lt (by omega)]
    push_cast [Nat.cast_sub hp₂]
    ring
  have hK6 : ∀ c x : ℝ, (K : ℝ) * (c * x) = c * (K * x) := fun c x => by ring
  have hγR : (outerExponent p N K : ℝ) = ((outerExponent p N K : ℤ) : ℝ) := rfl
  rw [rankDefect_of_one_half_le hy₃.le, sub_zero,
    ← outerExponent_min_eq_outerLimitingFunction hy₃ hy₂]
  have hγ := outerExponent_of_lt (N := N) hlt
  rw [natCast_smallClassCount, natCast_overlapCount, cast_outerRankBound, hvz] at hγ
  rw [hγR, hγ]
  push_cast
  simp only [posPart_def, hα, mul_add, mul_sub, hK6 6, mul_min_of_nonneg (ha := hK0.le),
    mul_max_of_nonneg (ha := hK0.le), mul_zero, mul_one, hc, hKy, e2, e3]
  have hU : |max 0 ((N : ℝ) + (K - p) - p + 1) - max ((K : ℝ) + N - 2 * p) 0| ≤ 1 :=
    (abs_max_zero_sub_max_zero_le _ _).trans (by rw [abs_le]; constructor <;> linarith)
  have hR : |max 0 ((K : ℝ) + 4 * N - 2 * p + 2) - max ((K : ℝ) + 4 * N - 2 * p) 0| ≤ 2 :=
    (abs_max_zero_sub_max_zero_le _ _).trans (by rw [abs_le]; constructor <;> linarith)
  have hM := (abs_min_sub_min_le_max (max 0 ((K : ℝ) + 4 * N - 2 * p + 2))
    ((p : ℝ) - 1 - N + max 0 ((N : ℝ) + (K - p) - p + 1))
    (max ((K : ℝ) + 4 * N - 2 * p) 0) ((p : ℝ) - N + max ((K : ℝ) + N - 2 * p) 0)).trans
    (max_le hR (by rw [abs_le] at hU ⊢; constructor <;> linarith))
  rw [abs_le] at hU hM ⊢
  constructor <;> linarith

/-- The near case `2 p ≤ K` of the outer exponent asymptotics, with error at most `10`. -/
theorem abs_neg_outerExponent_sub_le_of_le {n p : ℕ} (hp₁ : poleBound n < 3 * p)
    (hle : 2 * p ≤ poleBound n) :
    |-(outerExponent p (innerDegree n) (poleBound n) : ℝ) -
        poleBound n * (outerLimitingFunction (p / poleBound n) -
          rankDefect (p / poleBound n))| ≤ 10 := by
  set K := poleBound n with hKdef
  set N := innerDegree n with hNdef
  have hKN : (K : ℝ) = 40 * n := by simp [hKdef, poleBound]
  have hNN : (N : ℝ) = 3 * n := by simp [hNdef, innerDegree]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hα : (innerRatio : ℝ) = 3 / 40 := by norm_num [innerRatio]
  have hpK : 2 * (p : ℝ) ≤ K := by exact_mod_cast hle
  set y : ℝ := p / K with hy
  have hKy : (K : ℝ) * y = p := by
    rw [hy]
    field_simp
  have e2 : (K : ℝ) * (3 / 40) = N := by
    rw [hKN, hNN]
    ring
  have hy₁ : 1 / 3 < y := by
    have : (K : ℝ) < 3 * p := by exact_mod_cast hp₁
    rw [hy, lt_div_iff₀ hK0]
    linarith
  have hy₃ : y ≤ 1 / 2 := by
    rw [hy, div_le_iff₀ hK0]
    linarith
  have hvz : (vA p K : ℤ) = K - 2 * p := by
    have hv : vA p K = K - 2 * p := by
      rw [vA, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega : p ≤ K - p),
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hv]
    push_cast [Nat.cast_sub hle]
    ring
  have hK6 : ∀ c x : ℝ, (K : ℝ) * (c * x) = c * (K * x) := fun c x => by ring
  have hγR : (outerExponent p N K : ℝ) = ((outerExponent p N K : ℤ) : ℝ) := rfl
  rw [← outerExponent_eq_outerLimitingFunction_sub_rankDefect hy₁ hy₃]
  have hγ := outerExponent_of_le (N := N) hle
  rw [natCast_smallClassCount, natCast_overlapCount, cast_outerRankBound, hvz] at hγ
  rw [hγR, hγ]
  push_cast
  simp only [posPart_def, hα, mul_add, mul_sub, hK6, mul_min_of_nonneg (ha := hK0.le),
    mul_max_of_nonneg (ha := hK0.le), mul_zero, mul_one, hKy, e2]
  have hU : |max 0 ((N : ℝ) + (K - 2 * p) - p + 1) - max ((K : ℝ) + N - 3 * p) 0| ≤ 1 :=
    (abs_max_zero_sub_max_zero_le _ _).trans (by rw [abs_le]; constructor <;> linarith)
  rw [max_eq_right (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)] :
    (0 : ℝ) ≤ K + 4 * N - 2 * p + 2)]
  have hM : |min ((K : ℝ) + 4 * N - 2 * p + 2)
        ((p : ℝ) + max 0 ((N : ℝ) + (K - 2 * p) - p + 1)) -
        min ((K : ℝ) + 4 * N - 2 * p) ((p : ℝ) + max ((K : ℝ) + N - 3 * p) 0)| ≤ 2 :=
    (abs_min_sub_min_le_max ((K : ℝ) + 4 * N - 2 * p + 2)
    ((p : ℝ) + max 0 ((N : ℝ) + (K - 2 * p) - p + 1))
    ((K : ℝ) + 4 * N - 2 * p) ((p : ℝ) + max ((K : ℝ) + N - 3 * p) 0)).trans
    (max_le (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le] at hU ⊢; constructor <;> linarith))
  rw [abs_le] at hU hM ⊢
  constructor <;> linarith

/-- **The outer exponent asymptotics.** For `K = 40 n`, `N = 3 n` and `p` with
`K / 3 < p ≤ K`, `|-γ_p^out - K (R₀(p/K) - d_rk(p/K))| ≤ 20`. -/
@[zeta5irr "lem_gout_asymp"]
theorem abs_neg_outerExponent_sub_le {n p : ℕ} (hp₁ : poleBound n < 3 * p)
    (hp₂ : p ≤ poleBound n) :
    |-(outerExponent p (innerDegree n) (poleBound n) : ℝ) -
        poleBound n * (outerLimitingFunction (p / poleBound n) -
          rankDefect (p / poleBound n))| ≤ 20 := by
  rcases lt_or_ge (poleBound n) (2 * p) with h | h
  · exact (abs_neg_outerExponent_sub_le_of_lt hp₂ h).trans (by norm_num)
  · exact (abs_neg_outerExponent_sub_le_of_le hp₁ h).trans (by norm_num)

end Zeta5Irr
