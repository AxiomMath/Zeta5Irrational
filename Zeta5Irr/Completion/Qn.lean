/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.PrimeSum.QKM

/-!
# The polynomials `Q_n`

For an integer `n ≥ 200000`, the polynomial used in the completion of the irrationality proof
is the normalized polynomial with parameters `K = 40 n` and `M = 200`:
```
Q_n = Q_{40n, 200}.
```
The lower bound `n ≥ 200000` is exactly the condition `K ≥ 200 M²` of the normalized
polynomial for `K = 40 n`, `M = 200`.

## Main definitions

* `Zeta5Irr.Qn`: the polynomial `Q_n = Q_{40n, 200} ∈ ℝ[X]`.

## Implementation notes

* The normalized polynomial `Q_{K,M}` is indexed by `n` and `M` with `K = 40 n`, so `Q_n` is
  `normalizedPoly n 200`. It is an abbreviation, so that the API of the normalized polynomial
  (coefficients, evaluation, degree) applies to it directly.
* The hypothesis `n ≥ 200000` is not needed to write the polynomial down, so the definition is
  total; the hypothesis is carried by the results about `Q_n` that need it.
* As for `Q_{K,M}`, the coefficients are real numbers; that they are integers is a separate
  result.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The polynomial `Q_n = Q_{40n, 200} ∈ ℝ[X]`, used for `n ≥ 200000` in the completion of the
irrationality proof. -/
@[zeta5irr "def_Qn"]
noncomputable abbrev Qn (n : ℕ) : ℝ[X] :=
  normalizedPoly n 200

end Zeta5Irr
