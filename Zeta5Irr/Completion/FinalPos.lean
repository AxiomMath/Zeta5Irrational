/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Completion.Qn
public import Zeta5Irr.Completion.FinalPosK

/-!
# `Q_n(ξ)` is positive

Let `ξ = ζ(5)`. For every integer `n ≥ 200000`, `Q_n(ξ) > 0`. Indeed `Q_n = Q_{40n,200}`, and
`Q_{K,M}(ξ) > 0` for `M = 200 ≥ 40` and `K = 40 n`, a positive multiple of `40` with
`K ≥ 40 · 200000 = 200 · 200²`.

## Main results

* `Zeta5Irr.eval_Qn_zetaFive_pos`: `0 < Q_n(ξ)`.

## Implementation notes

The positivity of `Q_{K,M}(ξ)` holds for all `K = 40 n` and all `M`, without the hypotheses
`M ≥ 40`, `K > 0` and `K ≥ 200 M²`. Accordingly the hypothesis `n ≥ 200000` is not needed and
the result is stated for every natural number `n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- **`Q_n(ξ)` is positive.** For `ξ = ζ(5)`, `0 < Q_n(ξ)`; in the source this is stated for
`n ≥ 200000`, the range in which `Q_n` is used. -/
@[zeta5irr "lem_final_pos"]
theorem eval_Qn_zetaFive_pos (n : ℕ) : 0 < (Qn n).eval zetaFive :=
  eval_normalizedPoly_zetaFive_pos n 200

end Zeta5Irr
