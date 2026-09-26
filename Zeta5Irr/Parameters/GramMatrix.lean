/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.Parameters.PoleProductRange
public import Zeta5Irr.Parameters.MuX

/-!
# The matrix `G_K`

With the parameters `K = 40 n`, `N = 3 n` and `h = 37 n`, the matrix `G_K(X)` is the
`h × h` matrix over `ℚ[X]` whose `(i, j)` entry is the value of the rational functional
`μ_X` on the rational function `D_N(t) ^ 6 t ^ (i + j) / D_K(t)`, that is
`G_K(X)_{ij} = μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K})` for `0 ≤ i, j < h`.
Its entries depend on `i` and `j` only through `i + j`, so it is a Hankel matrix, and in
particular symmetric.

## Main definitions

* `Zeta5Irr.gramMatrix`: the matrix `G_K(X)`.

## Main results

* `Zeta5Irr.gramMatrix_apply`: the entries of `G_K(X)`.
* `Zeta5Irr.gramMatrix_isSymm`, `Zeta5Irr.gramMatrix_transpose`: `G_K(X)` is symmetric.

## Implementation notes

* The rows and columns are indexed by `Fin h`, and the exponent `i + j` is the sum of the
  underlying natural numbers.
* The set `{1, …, K}` is `Finset.Icc 1 K`, whose pole product is `D_K`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §2.1: the parameters, the functional, and the matrix.
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The matrix `G_K(X)`: the `h × h` matrix over `ℚ[X]` with entries
`G_K(X)_{ij} = μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K})`, where `K = 40 n`, `N = 3 n` and
`h = 37 n`. -/
@[zeta5irr "def_GK"]
noncomputable def gramMatrix (n : ℕ) :
    Matrix (Fin (matrixOrder n)) (Fin (matrixOrder n)) ℚ[X] :=
  Matrix.of fun i j => rationalFunctional (Finset.Icc 1 (poleBound n))
    (poleProductRange (innerDegree n) ℚ ^ 6 * X ^ ((i : ℕ) + j))

/-- The entries of `G_K(X)`: `G_K(X)_{ij} = μ_X(D_N(t) ^ 6 t ^ (i + j); {1, …, K})`. -/
@[zeta5irr "def_GK", simp]
theorem gramMatrix_apply (n : ℕ) (i j : Fin (matrixOrder n)) :
    gramMatrix n i j = rationalFunctional (Finset.Icc 1 (poleBound n))
      (poleProductRange (innerDegree n) ℚ ^ 6 * X ^ ((i : ℕ) + j)) :=
  rfl

/-- `G_K(X)` is symmetric. -/
theorem gramMatrix_isSymm (n : ℕ) : (gramMatrix n).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp only [gramMatrix_apply, add_comm]

/-- `G_K(X)ᵀ = G_K(X)`. -/
@[simp]
theorem gramMatrix_transpose (n : ℕ) : (gramMatrix n).transpose = gramMatrix n :=
  gramMatrix_isSymm n

end Zeta5Irr
