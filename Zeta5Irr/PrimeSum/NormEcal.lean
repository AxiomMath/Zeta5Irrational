/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LimitingFunctions.Sx
public import Zeta5Irr.LimitingFunctions.Nplus
public import Zeta5Irr.PrimeSum.NormDelta
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The error term `𝓔` in the splitting of the inner limiting function

With `α = 3/40`, `λ = 37/40`, the allocation remainder `s̃`, the base offset `ñ` and the
deviation `δ(x, z) = ℓ(x, z) - 2x`, the error term is
```
𝓔(x) = (2 s̃(x) (2 s̃(x) - 2 ñ(x)) - (2 s̃(x) - 2 ñ(x))₊ + {2 λ x} (1 - {2 λ x})) / 2
        + 9 ∫_0^{1/2} δ(α x, z)² dz - 3 ∫_0^{1/2} δ(x, z) δ(α x, z) dz.
```

## Main definitions

* `Zeta5Irr.innerSplitError`: the error term `𝓔(x)`.

## Main results

* `Zeta5Irr.innerSplitError_def`: the defining formula.

## Implementation notes

* The source defines `𝓔` only for `x ≥ 3`. The formula makes sense for every real `x`, so
  `𝓔` is defined on all of `ℝ`, and the restriction `x ≥ 3` is carried by the lemmas that
  use it.
* The two integrals are interval integrals over `[0, 1/2]`; the value of `δ(·, z)` at the
  endpoints `z = 0, 1/2`, where the source leaves `δ` undefined, does not affect them.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.5: the splitting of the inner limiting function.
-/

@[expose] public section

namespace Zeta5Irr

/-- The error term `𝓔(x)` in the splitting of the inner limiting function:
`(2s̃(2s̃ - 2ñ) - (2s̃ - 2ñ)₊ + {2λx}(1 - {2λx})) / 2 + 9 ∫_0^{1/2} δ(αx, z)² dz
- 3 ∫_0^{1/2} δ(x, z) δ(αx, z) dz`, with `α = 3/40` and `λ = 37/40`. The source restricts to
`x ≥ 3`; the formula is used for all real `x`. -/
@[zeta5irr "def_norm_Ecal"]
noncomputable def innerSplitError (x : ℝ) : ℝ :=
  (2 * allocationRemainder x * (2 * allocationRemainder x - 2 * baseHalfFract x) -
      (2 * allocationRemainder x - 2 * baseHalfFract x)⁺ +
      Int.fract (2 * (orderRatio : ℝ) * x) * (1 - Int.fract (2 * (orderRatio : ℝ) * x))) / 2 +
    9 * (∫ z in (0 : ℝ)..(1 / 2), ellDeviation ((innerRatio : ℝ) * x) z ^ 2) -
    3 * ∫ z in (0 : ℝ)..(1 / 2), ellDeviation x z * ellDeviation ((innerRatio : ℝ) * x) z

/-- Unfolding lemma for `𝓔`. -/
theorem innerSplitError_def (x : ℝ) :
    innerSplitError x =
      (2 * allocationRemainder x * (2 * allocationRemainder x - 2 * baseHalfFract x) -
          (2 * allocationRemainder x - 2 * baseHalfFract x)⁺ +
          Int.fract (2 * (orderRatio : ℝ) * x) *
            (1 - Int.fract (2 * (orderRatio : ℝ) * x))) / 2 +
        9 * (∫ z in (0 : ℝ)..(1 / 2), ellDeviation ((innerRatio : ℝ) * x) z ^ 2) -
        3 * ∫ z in (0 : ℝ)..(1 / 2),
          ellDeviation x z * ellDeviation ((innerRatio : ℝ) * x) z :=
  rfl

end Zeta5Irr
