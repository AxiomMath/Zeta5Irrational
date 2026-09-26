/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Completion.Qn
public import Zeta5Irr.DegreePositivity.GramDetDegree

/-!
# The degree of `Q_n`

The polynomial `Q_n = Q_{40n, 200} = m_{40n,200} S_{40n} Δ_{40n}` is a nonzero constant multiple
of the Gram determinant `Δ_{40n}`, so it has the same degree, namely `h = 37 n`.

## Main results

* `Zeta5Irr.natDegree_Qn`, `Zeta5Irr.degree_Qn`: `Q_n` has degree `37 n`.

## Implementation notes

* The source states the result for `n ≥ 200000`, the range in which `Q_n` is used. The
  argument does not use this bound: the normalizing factor `m_{40n,200}` and the scaling
  factor `S_{40n}` are nonzero for every `n`, and `Δ_{40n}` has degree `37 n` for every `n`.
  The results are therefore stated for every natural number `n`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §11 (Completion of the irrationality proof).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- **The degree of `Q_n`**, stated for `natDegree`: `Q_n` has degree `37 n`. -/
@[zeta5irr "lem_final_degree"]
theorem natDegree_Qn (n : ℕ) : (Qn n).natDegree = 37 * n := by
  rw [Qn, natDegree_normalizedPoly, natDegree_normalizedDet, natDegree_gramDet, matrixOrder]

/-- **The degree of `Q_n`**: `Q_n` has degree `37 n`. -/
@[zeta5irr "lem_final_degree"]
theorem degree_Qn (n : ℕ) : (Qn n).degree = (37 * n : ℕ) := by
  rw [Qn, degree_normalizedPoly, degree_normalizedDet, degree_gramDet, matrixOrder]

end Zeta5Irr
