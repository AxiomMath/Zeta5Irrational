/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InBa
public import Zeta5Irr.LocalEstimates.InEps

/-!
# The class dimensions `L_a`

For an odd prime `p`, an integer `M ≥ 40` and `1 ≤ a ≤ m°`, the inner range of the construction
assigns to the nonzero square class indexed by `a` the dimension
`L_a = T - b_a + ε_a`,
where `T` is the common class dimension, `b_a = 3 ℓ_N(a)` is the inner class order and `ε_a`
is the extras indicator.

## Main definitions

* `Zeta5Irr.innerClassDim`: the class dimension `L_a = T - b_a + ε_a`.
* `Zeta5Irr.classDimAt`: the dimension `L_s` of the class `s`, for `0 ≤ s ≤ m°`, where
  `L_0 = 4 M + 10` is the reserved zero-class dimension.
* `Zeta5Irr.rowPolyExponent`: the natural-number exponent `L_c`, i.e. `L_0` for `c = 0` and the
  truncation of `L_c` at `0` for `c ≥ 1`.

## Main results

* `Zeta5Irr.sub_innerClassOrder_le_innerClassDim`: `T - b_a ≤ L_a`.
* `Zeta5Irr.innerClassDim_le`: `L_a ≤ T - b_a + 1`.
* `Zeta5Irr.rowPolyExponent_eq_toNat_classDimAt`: `rowPolyExponent` is the truncation of
  `classDimAt` at `0`.

## Implementation notes

* Since `T` is an integer which can be negative, `L_a` is integer valued; its nonnegativity
  is a lemma which uses the hypotheses on `p` and `M`.
* The integers `K = 40 n`, `h = 37 n` and `N = 3 n` are functions of `n`, so `L_a` takes `n`
  as an argument along with `p`, `M` and `a`. The hypotheses that `p` is an odd prime,
  `M ≥ 40` and `1 ≤ a ≤ m°` are not needed to define `L_a`; they are carried by the lemmas
  which use them.
* An exponent is a natural number, so `rowPolyExponent` uses the truncation `max L_c 0`, which
  agrees with `L_c` whenever `L_c ≥ 0`, in particular in the range of parameters of the source.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

/-- The class dimension `L_a = T - b_a + ε_a`, where `T` is the common class dimension,
`b_a = 3 ℓ_N(a)` (with `N = 3 n`) is the inner class order and `ε_a` is the extras indicator. -/
@[zeta5irr "def_La"]
def innerClassDim (n p M a : ℕ) : ℤ :=
  commonClassDim n p M - innerClassOrder p (innerDegree n) a + extraIndicator n p M a

/-- Unfolding lemma for `innerClassDim`. -/
theorem innerClassDim_def (n p M a : ℕ) : innerClassDim n p M a =
    commonClassDim n p M - innerClassOrder p (innerDegree n) a + extraIndicator n p M a :=
  rfl

/-- `T - b_a ≤ L_a`. -/
theorem sub_innerClassOrder_le_innerClassDim (n p M a : ℕ) :
    commonClassDim n p M - innerClassOrder p (innerDegree n) a ≤ innerClassDim n p M a := by
  rw [innerClassDim_def]
  omega

/-- `L_a ≤ T - b_a + 1`. -/
theorem innerClassDim_le (n p M a : ℕ) :
    innerClassDim n p M a ≤ commonClassDim n p M - innerClassOrder p (innerDegree n) a + 1 := by
  have := extraIndicator_le_one n p M a
  rw [innerClassDim_def]
  omega

/-- The dimension `L_s` of the class `s`: `L_0 = 4 M + 10` is the reserved zero-class dimension,
and for `s ≥ 1`, `L_s = T - b_s + ε_s` is the class dimension `innerClassDim`. -/
def classDimAt (n p M s : ℕ) : ℤ :=
  if s = 0 then zeroClassDim M else innerClassDim n p M s

/-- `L_0 = 4 M + 10`. -/
@[simp]
theorem classDimAt_zero (n p M : ℕ) : classDimAt n p M 0 = zeroClassDim M := by
  simp [classDimAt]

/-- For `s ≠ 0`, `L_s` is the class dimension `T - b_s + ε_s`. -/
theorem classDimAt_of_ne_zero (n p M : ℕ) {s : ℕ} (hs : s ≠ 0) :
    classDimAt n p M s = innerClassDim n p M s := by
  simp [classDimAt, hs]

/-- The exponent `L_c` of the factor `(t + c²)` in the row polynomials: the reserved zero-class
dimension `L_0` for `c = 0`, and the class dimension `L_c` (truncated at `0`) for `c ≥ 1`. -/
def rowPolyExponent (n p M c : ℕ) : ℕ :=
  if c = 0 then zeroClassDim M else (innerClassDim n p M c).toNat

/-- The exponent of `t = t + 0²` is `L_0`. -/
@[simp]
theorem rowPolyExponent_zero (n p M : ℕ) : rowPolyExponent n p M 0 = zeroClassDim M := rfl

/-- For `c ≠ 0` the exponent of `(t + c²)` is the truncation of `L_c` at `0`. -/
theorem rowPolyExponent_of_ne_zero (n p M : ℕ) {c : ℕ} (hc : c ≠ 0) :
    rowPolyExponent n p M c = (innerClassDim n p M c).toNat := by simp [rowPolyExponent, hc]

/-- If `L_c ≥ 0` then the exponent of `(t + c²)` is `L_c`. -/
theorem cast_rowPolyExponent_of_ne_zero (n p M : ℕ) {c : ℕ} (hc : c ≠ 0)
    (h : 0 ≤ innerClassDim n p M c) :
    (rowPolyExponent n p M c : ℤ) = innerClassDim n p M c := by
  rw [rowPolyExponent_of_ne_zero n p M hc, Int.toNat_of_nonneg h]

/-- The exponent of `(t + c²)` is the truncation of `L_c` at `0`. -/
theorem rowPolyExponent_eq_toNat_classDimAt (n p M c : ℕ) :
    rowPolyExponent n p M c = (classDimAt n p M c).toNat := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [rowPolyExponent_zero, classDimAt_zero, Int.toNat_natCast]
  · rw [rowPolyExponent_of_ne_zero n p M hc, classDimAt_of_ne_zero n p M hc]

end Zeta5Irr
