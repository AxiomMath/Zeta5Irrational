/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Basic
public import Zeta5Irr.LocalEstimates.InMstar
public import Zeta5Irr.LocalEstimates.MA
public import Zeta5Irr.LocalEstimates.InL0

/-!
# The common class dimension `T`

For an odd prime `p` and an integer `M ≥ 40`, the inner range of the construction distributes
the `h - L₀ + 3 (N - m_N)` dimensions left over after the zero class as evenly as possible
among the `m°` nonzero square classes. Each class receives the common dimension
`T = ⌊(h - L₀ + 3 (N - m_N)) / m°⌋`, and the remainder is handed out as extras.

## Main definitions

* `Zeta5Irr.commonClassDim`: the common class dimension
  `T = ⌊(h - L₀ + 3 (N - m_N)) / m°⌋`.

## Main results

* `Zeta5Irr.commonClassDim_eq_floor`: `T` is the floor of the quotient in any linearly ordered
  field.
* `Zeta5Irr.mStar_mul_commonClassDim_le`, `Zeta5Irr.lt_mStar_mul_commonClassDim_add`:
  `m° T ≤ h - L₀ + 3 (N - m_N) < m° T + m°` when `m° > 0`.
* `Zeta5Irr.lt_mul_and_lt_of_div_lt_of_sq_le`, `Zeta5Irr.forty_mul_mA_innerDegree_lt`: the
  inequalities `K < p M`, `200 M < p` and `40 m_N < 3 M` of the inner range of parameters.

## Implementation notes

* The numerator `h - L₀ + 3 (N - m_N)` can be negative when `M` is large compared with `n`,
  so `T` is an integer, computed by the Euclidean division `Int.ediv`. Since `m° ≥ 0` this
  division is the floor of the quotient (and `T = 0` when `m° = 0`), see
  `commonClassDim_eq_floor`.
* The integers `h = 37 n` and `N = 3 n` are functions of `n`, so `T` takes `n` as an argument
  along with `p` and `M`. The hypotheses that `p` is an odd prime and `M ≥ 40` are not needed
  to define `T`; they are carried by the lemmas which use them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The common class dimension `T = ⌊(h - L₀ + 3 (N - m_N)) / m°⌋`, where `h = 37 n`,
`N = 3 n`, `L₀ = 4 M + 10`, `m_N = ⌊N / p⌋` and `m° = (p - 1) / 2`. -/
@[zeta5irr "def_in_T"]
def commonClassDim (n p M : ℕ) : ℤ :=
  ((matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n))) /
    (mStar p : ℤ)

/-- Unfolding lemma for `commonClassDim`. -/
theorem commonClassDim_def (n p M : ℕ) :
    commonClassDim n p M =
      ((matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n))) /
        (mStar p : ℤ) :=
  rfl

/-- The common class dimension is the floor of the quotient
`(h - L₀ + 3 (N - m_N)) / m°` computed in any linearly ordered field. -/
theorem commonClassDim_eq_floor {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [FloorRing k] (n p M : ℕ) :
    commonClassDim n p M =
      ⌊((matrixOrder n : k) - zeroClassDim M + 3 * ((innerDegree n : k) - mA p (innerDegree n))) /
        (mStar p : k)⌋ := by
  rw [Int.floor_div_natCast, commonClassDim_def]
  congr 1
  exact_mod_cast (Int.floor_intCast (R := k)
    ((matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n)))).symm

/-- `m° T ≤ h - L₀ + 3 (N - m_N)`. -/
theorem mStar_mul_commonClassDim_le {n p M : ℕ} (hp : 0 < mStar p) :
    (mStar p : ℤ) * commonClassDim n p M ≤
      (matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n)) :=
  Int.mul_ediv_self_le (by omega)

/-- `h - L₀ + 3 (N - m_N) < m° T + m°`. -/
theorem lt_mStar_mul_commonClassDim_add {n p M : ℕ} (hp : 0 < mStar p) :
    (matrixOrder n : ℤ) - zeroClassDim M + 3 * ((innerDegree n : ℤ) - mA p (innerDegree n)) <
      (mStar p : ℤ) * commonClassDim n p M + mStar p :=
  Int.lt_mul_ediv_self_add (by omega)

section Parameters

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- If `0 < M` and `K / M < p` in an ordered field, then `K < p M`. -/
theorem lt_mul_of_div_lt {K M p : ℕ} (hM : 0 < M) (h : (K : α) / M < p) : K < p * M := by
  rw [div_lt_iff₀ (by exact_mod_cast hM)] at h
  exact_mod_cast h

/-- The inner-range parameters: if `0 < M`, `200 M² ≤ K` and `K / M < p` in an ordered field,
then `K < p M` and `200 M < p`. -/
theorem lt_mul_and_lt_of_div_lt_of_sq_le {K M p : ℕ} (hM : 0 < M) (hK : 200 * M ^ 2 ≤ K)
    (h : (K : α) / M < p) : K < p * M ∧ 200 * M < p := by
  have hpM := lt_mul_of_div_lt hM h
  refine ⟨hpM, Nat.lt_of_mul_lt_mul_right (a := M) ?_⟩
  rw [show 200 * M * M = 200 * M ^ 2 by ring]
  exact hK.trans_lt hpM

/-- In the inner range, where `K = 40 n < p M`, `40 m_N < 3 M` with `N = 3 n`. -/
theorem forty_mul_mA_innerDegree_lt {n p M : ℕ} (hpM : poleBound n < p * M) :
    40 * mA p (innerDegree n) < 3 * M := by
  simp only [mA, innerDegree, poleBound] at hpM ⊢
  have h1 : 3 * n / p * p ≤ 3 * n := Nat.div_mul_le_self _ _
  by_contra! h
  have : 3 * M * p ≤ 40 * (3 * n / p) * p := Nat.mul_le_mul_right p h
  nlinarith

end Parameters

end Zeta5Irr
