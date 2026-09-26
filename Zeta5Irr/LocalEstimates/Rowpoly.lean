/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalEstimates.La

/-!
# The row polynomials `Ψ_{a,i}`

For an odd prime `p`, an integer `M ≥ 40`, an index `0 ≤ a ≤ m°` and an integer `0 ≤ i < L_a`,
the inner range of the construction uses the row polynomial
`Ψ_{a,i}(t) = (∏_{0 ≤ c ≤ m°, c ≠ a} (t + c²)^{L_c}) (t + a²)^i`,
where `L_0 = 4 M + 10` is the reserved zero-class dimension and `L_c`, `1 ≤ c ≤ m°`, are the
class dimensions. The factor `(t + a²)^{L_a}` of the full product is replaced by the lower power
`(t + a²)^i`, so these polynomials form a basis distributing over the square classes.

## Main definitions

* `Zeta5Irr.rowPoly`: the row polynomial `Ψ_{a,i} ∈ ℚ[t]`.

## Main results

* `Zeta5Irr.rowPoly_monic`: `Ψ_{a,i}` is monic.
* `Zeta5Irr.natDegree_rowPoly`: `deg Ψ_{a,i} = ∑_{c ≠ a} L_c + i`.

## Implementation notes

* The class dimensions `L_c`, `c ≥ 1`, are integer valued in their definition (their
  nonnegativity is a lemma requiring the hypotheses on `p` and `M`), whereas an exponent is a
  natural number, so the exponents are `Zeta5Irr.rowPolyExponent`, the truncation of `L_c`
  at `0`.
* The hypotheses that `p` is an odd prime, `M ≥ 40`, `a ≤ m°` and `i < L_a` are not needed to
  define `Ψ_{a,i}`; they are carried by the lemmas which use them. As for `L_a`, the integers
  `K`, `h`, `N` depend on `n`, so `Ψ_{a,i}` also takes `n` as an argument.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.4 (The inner range: the distributing basis).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

/-- The row polynomial
`Ψ_{a,i}(t) = (∏_{0 ≤ c ≤ m°, c ≠ a} (t + c²)^{L_c}) (t + a²)^i`. -/
@[zeta5irr "def_rowpoly"]
noncomputable def rowPoly (n p M a i : ℕ) : ℚ[X] :=
  (∏ c ∈ Finset.range (mStar p + 1) \ {a}, (X + C ((c : ℚ) ^ 2)) ^ rowPolyExponent n p M c) *
    (X + C ((a : ℚ) ^ 2)) ^ i

/-- Unfolding lemma for `rowPoly`. -/
theorem rowPoly_def (n p M a i : ℕ) : rowPoly n p M a i =
    (∏ c ∈ Finset.range (mStar p + 1) \ {a}, (X + C ((c : ℚ) ^ 2)) ^ rowPolyExponent n p M c) *
      (X + C ((a : ℚ) ^ 2)) ^ i :=
  rfl

/-- The row polynomial `Ψ_{a,i}` is monic. -/
theorem rowPoly_monic (n p M a i : ℕ) : (rowPoly n p M a i).Monic :=
  (monic_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).pow _).mul ((monic_X_add_C _).pow _)

/-- The degree of `Ψ_{a,i}` is `∑_{c ≠ a} L_c + i`. -/
theorem natDegree_rowPoly (n p M a i : ℕ) : (rowPoly n p M a i).natDegree =
    ∑ c ∈ Finset.range (mStar p + 1) \ {a}, rowPolyExponent n p M c + i := by
  rw [rowPoly_def, (monic_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).pow _).natDegree_mul
    ((monic_X_add_C _).pow _), natDegree_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).pow _]
  simp only [natDegree_pow, natDegree_X_add_C, mul_one]

end Zeta5Irr
