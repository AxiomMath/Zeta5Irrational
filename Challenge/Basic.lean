/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

namespace Zeta5Irr.Challenge

/-- **`thm_main` — the main theorem.** `ζ(5)`, the real value of Mathlib's `riemannZeta 5`,
is irrational. -/
theorem thm_main : Irrational (riemannZeta 5).re :=
  sorry

/-- **`thm_tsum` — the series form.** `∑_{v ≥ 1} v⁻⁵` is irrational; the sum runs over all
`v : ℕ`, and the `v = 0` term `1 / 0 ^ 5` is `0`. -/
theorem thm_tsum : Irrational (∑' n : ℕ, (1 / n ^ 5 : ℝ)) :=
  sorry

end Zeta5Irr.Challenge
