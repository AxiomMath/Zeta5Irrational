/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Completion.Qn
public import Zeta5Irr.Completion.FinalPos
public import Zeta5Irr.Completion.FinalLimsup
public import Zeta5Irr.ExactIntegrals.Margin200

/-!
# Exponential decay of `Q_n(ξ)`

Let `ξ = ζ(5)`. There is an integer `n₀ ≥ 200000` such that
```
Q_n(ξ) < exp (-(139/5) n²)
```
for every integer `n ≥ n₀`.

Since `-1600 (A_200 + U) > 139/5`, the real number `b = -139/8000` satisfies `b > A_200 + U`.
The combined `K²`-scale bound at `M = 200` then gives `K⁻² log Q_{K,200}(ξ) < b` for all large
`n`, where `K = 40 n`. Multiplying by `K² = 1600 n²` gives `log Q_n(ξ) < -(139/5) n²`, and since
`Q_n(ξ) > 0` this is the claimed bound.

## Main results

* `Zeta5Irr.eval_Qn_zetaFive_lt_exp`: there is `n₀ ≥ 200000` with
  `Q_n(ξ) < exp (-(139/5) n²)` for all `n ≥ n₀`.

## Implementation notes

The source fixes `ε = δ / 3200` with `δ = -1600 (A_200 + U) - 139/5` and compares with
`A_200 + U + ε`; this is the same as comparing with the threshold `-139/8000`, which lies
strictly between `A_200 + U` and `A_200 + U + ε`, and that simpler threshold is used here.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

open Filter Polynomial

namespace Zeta5Irr

/-- **Exponential decay of `Q_n(ξ)`.** For `ξ = ζ(5)` there is an integer `n₀ ≥ 200000` such
that `Q_n(ξ) < exp (-(139/5) n²)` for every integer `n ≥ n₀`. -/
@[zeta5irr "prop_final_decay"]
theorem eval_Qn_zetaFive_lt_exp :
    ∃ n₀ : ℕ, 200000 ≤ n₀ ∧
      ∀ n ≥ n₀, (Qn n).eval zetaFive < Real.exp (-(139 / 5) * (n : ℝ) ^ 2) := by
  have hb : AM 200 + energyMargin < -139 / 8000 := by
    linarith [lt_neg_mul_AM_two_hundred_add_energyMargin]
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_log_eval_normalizedPoly_div_sq_lt (M := 200) (by norm_num) (by norm_num) hb)
  refine ⟨max N 200000, le_max_right _ _, fun n hn => ?_⟩
  have h := hN n (le_of_max_le_left hn)
  have hn0 : (0 : ℝ) < n := by
    have : 200000 ≤ n := le_of_max_le_right hn
    exact_mod_cast (by omega : 0 < n)
  have hK : ((poleBound n : ℕ) : ℝ) ^ 2 = 1600 * (n : ℝ) ^ 2 := by
    simp only [poleBound]; push_cast; ring
  rw [hK, div_lt_iff₀ (by positivity)] at h
  rw [← Real.log_lt_iff_lt_exp (eval_Qn_zetaFive_pos n)]
  linarith

end Zeta5Irr
