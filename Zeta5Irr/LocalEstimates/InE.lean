/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InT

/-!
# The number of extras `E`

For an odd prime `p` and an integer `M ≥ 40`, the inner range of the construction distributes
the `S = h - L₀ + 3 (N - m_N)` dimensions left over after the zero class among the `m°`
nonzero square classes: each class receives the common dimension `T = ⌊S / m°⌋`, and the
`E = S - m° T` dimensions that remain are handed out one at a time as extras.

## Main definitions

* `Zeta5Irr.extraCount`: the number of extras `E = h - L₀ + 3 (N - m_N) - m° T`.

## Main results

* `Zeta5Irr.mStar_mul_commonClassDim_add_extraCount`: `m° T + E = h - L₀ + 3 (N - m_N)`.
* `Zeta5Irr.extraCount_eq_emod`: `E` is the remainder of `h - L₀ + 3 (N - m_N)` modulo `m°`.

## Implementation notes

* Like `T`, the number `E` is an integer: it is a difference of integers, and it is only
  shown to be nonnegative (when `m° > 0`) after the fact.
* The integers `h = 37 n` and `N = 3 n` are functions of `n`, so `E` takes `n` as an argument
  along with `p` and `M`. The hypotheses that `p` is an odd prime and `M ≥ 40` are not needed
  to define `E`; they are carried by the lemmas which use them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The number of extras `E = h - L₀ + 3 (N - m_N) - m° T`, where `h = 37 n`, `N = 3 n`,
`L₀ = 4 M + 10`, `m_N = ⌊N / p⌋`, `m° = (p - 1) / 2` and `T` is the common class
dimension. -/
@[zeta5irr "def_in_E"]
def extraCount (n p M : ℕ) : ℤ :=
  (matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n)) -
    (mStar p : ℤ) * commonClassDim n p M

/-- Unfolding lemma for `extraCount`. -/
theorem extraCount_def (n p M : ℕ) :
    extraCount n p M =
      (matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n)) -
        (mStar p : ℤ) * commonClassDim n p M :=
  rfl

/-- `m° T + E = h - L₀ + 3 (N - m_N)`. -/
theorem mStar_mul_commonClassDim_add_extraCount (n p M : ℕ) :
    (mStar p : ℤ) * commonClassDim n p M + extraCount n p M =
      (matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n)) := by
  rw [extraCount_def]
  ring

/-- The number of extras is the remainder of `h - L₀ + 3 (N - m_N)` modulo `m°`. -/
theorem extraCount_eq_emod (n p M : ℕ) :
    extraCount n p M =
      ((matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n))) %
        (mStar p : ℤ) := by
  rw [extraCount_def, commonClassDim_def, Int.emod_def]

end Zeta5Irr
