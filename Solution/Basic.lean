/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Completion.Tsum

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace Zeta5Irr.Challenge

/-- **`thm_main` — the main theorem.** `ζ(5)`, the real value of Mathlib's `riemannZeta 5`,
is irrational. -/
theorem thm_main : Irrational (riemannZeta 5).re :=
  irrational_zetaFive

/-- **`thm_tsum` — the series form.** `∑_{v ≥ 1} v⁻⁵` is irrational; the sum runs over all
`v : ℕ`, and the `v = 0` term `1 / 0 ^ 5` is `0`. -/
theorem thm_tsum : Irrational (∑' n : ℕ, (1 / n ^ 5 : ℝ)) :=
  irrational_tsum_one_div_nat_pow_five

end Zeta5Irr.Challenge
