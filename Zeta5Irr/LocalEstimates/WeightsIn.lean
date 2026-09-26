/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InBa
public import Zeta5Irr.LocalEstimates.Za

/-!
# The weights `w_{a,i}` of the inner range

For an odd prime `p`, an integer `M ≥ 40`, an index `0 ≤ a ≤ m°` and an integer `0 ≤ i < L_a`,
the weights of the inner range are
`w_{a,i} = i + b_a - (ℓ_K(a) + 4) / 2` if `a ≥ 1`, and
`w_{0,i} = min(2 i + 6 m_N - m_K + 1/2, min_{1 ≤ c ≤ m°} (Z_c - (ℓ_K(c) + 4) / 2))`.
Here `K = 40 n`, `N = 3 n`, `m_A = ⌊A / p⌋`, `b_a = 3 ℓ_N(a)` and `Z_c = T + ε_c`.

## Main definitions

* `Zeta5Irr.innerWeight`: the weight `w_{a,i}`.

## Main results

* `Zeta5Irr.innerWeight_of_ne_zero`: the formula `i + b_a - (ℓ_K(a) + 4) / 2` for `a ≠ 0`.
* `Zeta5Irr.innerWeight_zero`: the formula for `a = 0`, with the inner minimum written as
  `Finset.inf'`, when `1 ≤ m°`.
* `Zeta5Irr.innerWeight_zero_le_left`, `Zeta5Irr.innerWeight_zero_le`: `w_{0,i}` is at most
  each of the quantities it is the minimum of.
* `Zeta5Irr.le_innerWeight_zero`: the universal property of the minimum.

## Implementation notes

* The value is rational, since half-integers occur.
* The integers `K = 40 n` and `N = 3 n` are functions of `n`, so `w_{a,i}` takes `n` as an
  argument along with `p`, `M`, `a` and `i`. The hypotheses that `p` is an odd prime, `M ≥ 40`,
  `a ≤ m°` and `i < L_a` are not needed to write the formula down, so the definition is total.
* The minimum in the case `a = 0` is written as `Finset.fold min`, starting from
  `2 i + 6 m_N - m_K + 1/2`, over `c ∈ [1, m°]`. This is total; when `m° ≥ 1` (for instance
  when `p` is an odd prime) it agrees with the source's formula, see
  `Zeta5Irr.innerWeight_zero`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.6: the inner range, the weights.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The weight `w_{a,i}` of the inner range: for `a ≠ 0` it is `i + b_a - (ℓ_K(a) + 4) / 2`,
and for `a = 0` it is `min(2 i + 6 m_N - m_K + 1/2, min_{1 ≤ c ≤ m°} (Z_c - (ℓ_K(c) + 4) / 2))`.
Here `K = 40 n`, `N = 3 n`, `ℓ_K = ellA p K`, `b_a = innerClassOrder p N a`, `m_A = mA p A`
and `Z_c = classDim n p M c`. -/
@[zeta5irr "def_weights_in"]
def innerWeight (n p M a i : ℕ) : ℚ :=
  if a = 0 then
    (Icc 1 (mStar p)).fold min
      (2 * (i : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2)
      (fun c => (classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2)
  else
    (i : ℚ) + innerClassOrder p (innerDegree n) a - ((ellA p (poleBound n) a : ℚ) + 4) / 2

/-- For `a ≠ 0`, `w_{a,i} = i + b_a - (ℓ_K(a) + 4) / 2`. -/
theorem innerWeight_of_ne_zero (n p M : ℕ) {a : ℕ} (ha : a ≠ 0) (i : ℕ) :
    innerWeight n p M a i =
      (i : ℚ) + innerClassOrder p (innerDegree n) a - ((ellA p (poleBound n) a : ℚ) + 4) / 2 :=
  by simp [innerWeight, ha]

/-- `w_{0,i}` as a `Finset.fold min`, valid without any hypothesis on `p`. -/
theorem innerWeight_zero_eq_fold (n p M i : ℕ) :
    innerWeight n p M 0 i =
      (Icc 1 (mStar p)).fold min
        (2 * (i : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2)
        (fun c => (classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2) :=
  rfl

/-- If `1 ≤ m°` (for instance, if `p` is an odd prime), then
`w_{0,i} = min(2 i + 6 m_N - m_K + 1/2, min_{1 ≤ c ≤ m°} (Z_c - (ℓ_K(c) + 4) / 2))`. -/
theorem innerWeight_zero (n p M i : ℕ) (hp : 1 ≤ mStar p) :
    innerWeight n p M 0 i =
      min (2 * (i : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2)
        ((Icc 1 (mStar p)).inf' (nonempty_Icc.2 hp)
          (fun c => (classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2)) := by
  rw [innerWeight_zero_eq_fold]
  refine le_antisymm (le_min ?_ ?_) ((le_fold_min _).2 ⟨min_le_left _ _, fun c hc => ?_⟩)
  · exact (fold_min_le _).2 (.inl le_rfl)
  · refine le_inf' _ _ fun c hc => (fold_min_le _).2 (.inr ⟨c, hc, le_rfl⟩)
  · exact (min_le_right _ _).trans (inf'_le _ hc)

/-- `w_{0,i} ≤ 2 i + 6 m_N - m_K + 1/2`. -/
theorem innerWeight_zero_le_left (n p M i : ℕ) :
    innerWeight n p M 0 i ≤
      2 * (i : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2 := by
  rw [innerWeight_zero_eq_fold]
  exact (fold_min_le _).2 (.inl le_rfl)

/-- For `1 ≤ c ≤ m°`, `w_{0,i} ≤ Z_c - (ℓ_K(c) + 4) / 2`. -/
theorem innerWeight_zero_le (n p M i : ℕ) {c : ℕ} (hc : c ∈ Icc 1 (mStar p)) :
    innerWeight n p M 0 i ≤
      (classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2 := by
  rw [innerWeight_zero_eq_fold]
  exact (fold_min_le _).2 (.inr ⟨c, hc, le_rfl⟩)

/-- A rational number bounded above by `2 i + 6 m_N - m_K + 1/2` and by every
`Z_c - (ℓ_K(c) + 4) / 2`, `1 ≤ c ≤ m°`, is at most `w_{0,i}`. -/
theorem le_innerWeight_zero {n p M i : ℕ} {x : ℚ}
    (h₀ : x ≤ 2 * (i : ℚ) + 6 * mA p (innerDegree n) - mA p (poleBound n) + 1 / 2)
    (h : ∀ c ∈ Icc 1 (mStar p),
      x ≤ (classDim n p M c : ℚ) - ((ellA p (poleBound n) c : ℚ) + 4) / 2) :
    x ≤ innerWeight n p M 0 i := by
  rw [innerWeight_zero_eq_fold]
  exact (le_fold_min _).2 ⟨h₀, h⟩

end Zeta5Irr
