/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.InEps

/-!
# The class dimension `Z_a`

For an odd prime `p`, an integer `M ≥ 40` and `1 ≤ a ≤ m°`, the square class `a` of the inner
range receives the common dimension `T` together with the extra `ε_a ∈ {0, 1}`, so its total
dimension is `Z_a = T + ε_a`.

## Main definitions

* `Zeta5Irr.classDim`: the class dimension `Z_a = T + ε_a`.

## Main results

* `Zeta5Irr.commonClassDim_le_classDim`, `Zeta5Irr.classDim_le_commonClassDim_add_one`:
  `T ≤ Z_a ≤ T + 1`.
* `Zeta5Irr.classDim_sub_classDim`: `Z_s - Z_a = ε_s - ε_a`.
* `Zeta5Irr.sum_classDim`: if `0 ≤ E ≤ m°` then `∑_{1 ≤ a ≤ m°} Z_a = m° T + E`.

## Implementation notes

* Since `T` is an integer (it may be negative for `M` large compared with `n`), `Z_a` is
  integer valued.
* As for `T` and `ε_a`, the integers `K = 40 n`, `h = 37 n` and `N = 3 n` are functions of `n`,
  so `Z_a` takes `n` as an argument along with `p`, `M` and `a`. The hypotheses that `p` is an
  odd prime, `M ≥ 40` and `1 ≤ a ≤ m°` are not needed to define `Z_a`; they are carried by the
  lemmas which use them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.3: the inner range, dimensions.
-/

@[expose] public section

namespace Zeta5Irr

open Finset

/-- The class dimension `Z_a = T + ε_a` of the square class `a` in the inner range, where `T`
is the common class dimension and `ε_a` the extras indicator. -/
@[zeta5irr "def_Za"]
def classDim (n p M a : ℕ) : ℤ :=
  commonClassDim n p M + extraIndicator n p M a

/-- Unfolding lemma for `classDim`. -/
theorem classDim_def (n p M a : ℕ) :
    classDim n p M a = commonClassDim n p M + extraIndicator n p M a :=
  rfl

/-- `T ≤ Z_a`. -/
theorem commonClassDim_le_classDim (n p M a : ℕ) : commonClassDim n p M ≤ classDim n p M a := by
  rw [classDim_def]
  omega

/-- `Z_a ≤ T + 1`. -/
theorem classDim_le_commonClassDim_add_one (n p M a : ℕ) :
    classDim n p M a ≤ commonClassDim n p M + 1 := by
  have := extraIndicator_le_one n p M a
  rw [classDim_def]
  omega

/-- `Z_s - Z_a = ε_s - ε_a`. -/
theorem classDim_sub_classDim (n p M s a : ℕ) :
    classDim n p M s - classDim n p M a =
      (extraIndicator n p M s : ℤ) - extraIndicator n p M a := by
  simp only [classDim_def]
  ring

/-- If `0 ≤ E ≤ m°`, then `∑_{1 ≤ a ≤ m°} Z_a = m° T + E`. -/
theorem sum_classDim {n p M : ℕ} (h₀ : 0 ≤ extraCount n p M)
    (h₁ : extraCount n p M ≤ mStar p) :
    ∑ a ∈ Icc 1 (mStar p), classDim n p M a =
      mStar p * commonClassDim n p M + extraCount n p M := by
  simp only [classDim_def, sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right,
    nsmul_eq_mul]
  rw [← sum_extraIndicator h₀ h₁]
  push_cast
  rfl

end Zeta5Irr
