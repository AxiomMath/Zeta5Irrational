/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.QRK
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# The pole-deleted product `F_{K,r}`

For `K ≥ 1` and `r ∈ R_K`, the pole-deleted product is the rational function
`F_{K,r} = (K!)² / ∏_{s ∈ R_K \ {r}} (x - s) ∈ ℚ(x)`,
obtained from `(K!)² / E_{R_K}(x)` by removing the simple pole at `x = r`.

## Main definitions

* `Zeta5Irr.poleDeletedDen R K r`: the denominator `∏_{s ∈ R_K \ {r}} (X - s) ∈ R[X]`, an
  abbreviation for the pole polynomial `intPoleProduct ((puncturedIcc K).erase r) R`.
* `Zeta5Irr.poleDeletedProduct K r`: the rational function `F_{K,r} ∈ ℚ(x)`.
* `Zeta5Irr.poleDeletedProductAt K r x`: the value `(K!)² / ∏_{s ∈ R_K \ {r}} (x - s)` in a field.

## Main results

* `Zeta5Irr.poleDeletedProductAt_ne_zero`: `F_{K,r}(x) ≠ 0` away from the poles, in
  characteristic zero.
* `Zeta5Irr.poleDeletedProductAt_mul_prod`: `F_{K,r}(x) ∏_{s ≠ r} (x - s) = (K!)²` away from
  the poles.
* `Zeta5Irr.eval_poleDeletedProduct`: evaluating the rational function `F_{K,r}` at a point
  of a characteristic-zero field where the denominator does not vanish gives
  `poleDeletedProductAt K r x`.

## Implementation notes

* The source requires `K ≥ 1` and `r ∈ R_K`. The definitions make sense for every `K : ℕ` and
  `r : ℤ`: when `r ∉ R_K` nothing is deleted and the denominator is `E_{R_K}`. Hypotheses are
  added only to the lemmas that need them.
* The consumers of `F_{K,r}` evaluate it at points of `ℤ_p` and bound valuations there, so
  besides the element `poleDeletedProduct K r` of `ℚ(x)` there is the pointwise function
  `poleDeletedProductAt K r` on an arbitrary field, and `eval_poleDeletedProduct` identifies
  the two away from the poles. The pointwise function is the division in the field, so it
  takes the junk value `0` at a pole. Since `RatFunc.eval` requires its source and target to
  live in the same universe, `eval_poleDeletedProduct` is stated for fields `F : Type`, which
  covers `ℚ_[p]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6: small primes.
-/

@[expose] public section

namespace Zeta5Irr

open Finset Polynomial Nat

/-- The denominator `∏_{s ∈ R_K \ {r}} (X - s)` of the pole-deleted product `F_{K,r}`, as a
polynomial over a commutative ring `R`: the pole polynomial `E_{R_K \ {r}}`. -/
noncomputable abbrev poleDeletedDen (R : Type*) [CommRing R] (K : ℕ) (r : ℤ) : R[X] :=
  intPoleProduct ((puncturedIcc K).erase r) R

/-- The pole-deleted product `F_{K,r} = (K!)² / ∏_{s ∈ R_K \ {r}} (x - s)`, an element of the
field of rational functions `ℚ(x)`. -/
@[zeta5irr "def_fr"]
noncomputable def poleDeletedProduct (K : ℕ) (r : ℤ) : RatFunc ℚ :=
  RatFunc.C ((K ! : ℚ) ^ 2) / algebraMap ℚ[X] (RatFunc ℚ) (poleDeletedDen ℚ K r)

/-- The value `F_{K,r}(x) = (K!)² / ∏_{s ∈ R_K \ {r}} (x - s)` of the pole-deleted product at a
point `x` of a field `F`. It takes the junk value `0` at the points of `R_K \ {r}`. -/
@[zeta5irr "def_fr"]
noncomputable def poleDeletedProductAt {F : Type*} [Field F] (K : ℕ) (r : ℤ) (x : F) : F :=
  (K ! : F) ^ 2 / ∏ s ∈ (puncturedIcc K).erase r, (x - s)

section At

variable {F : Type*} [Field F]

/-- `F_{K,r}(x)` is `(K!)²` divided by the value of the denominator polynomial at `x`. -/
theorem poleDeletedProductAt_def (K : ℕ) (r : ℤ) (x : F) :
    poleDeletedProductAt K r x = (K ! : F) ^ 2 / (poleDeletedDen F K r).eval x := by
  rw [eval_intPoleProduct, poleDeletedProductAt]

/-- Away from the poles, `F_{K,r}(x) ∏_{s ∈ R_K \ {r}} (x - s) = (K!)²`. -/
theorem poleDeletedProductAt_mul_prod {K : ℕ} {r : ℤ} {x : F}
    (hx : ∀ s ∈ (puncturedIcc K).erase r, x ≠ s) :
    poleDeletedProductAt K r x * ∏ s ∈ (puncturedIcc K).erase r, (x - s) = (K ! : F) ^ 2 := by
  have h : ∏ s ∈ (puncturedIcc K).erase r, (x - s) ≠ 0 := by
    rw [← eval_intPoleProduct]; exact (eval_intPoleProduct_ne_zero_iff _ _).2 hx
  rw [poleDeletedProductAt, div_mul_cancel₀ _ h]

/-- In characteristic zero, `F_{K,r}(x) ≠ 0` away from the poles. -/
theorem poleDeletedProductAt_ne_zero [CharZero F] {K : ℕ} {r : ℤ} {x : F}
    (hx : ∀ s ∈ (puncturedIcc K).erase r, x ≠ s) : poleDeletedProductAt K r x ≠ 0 := by
  have h : ∏ s ∈ (puncturedIcc K).erase r, (x - s) ≠ 0 := by
    rw [← eval_intPoleProduct]; exact (eval_intPoleProduct_ne_zero_iff _ _).2 hx
  rw [poleDeletedProductAt]
  exact div_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 K.factorial_ne_zero)) h

/-- The value of `F_{K,r}` at `r ∈ R_K` itself is `(K!)² / ∏_{s ∈ R_K \ {r}} (r - s)`, which is
nonzero in characteristic zero. -/
theorem poleDeletedProductAt_self_ne_zero [CharZero F] (K : ℕ) (r : ℤ) :
    poleDeletedProductAt K r (r : F) ≠ 0 := by
  refine poleDeletedProductAt_ne_zero fun s hs h => ?_
  exact (ne_of_mem_erase hs) (Int.cast_injective h).symm

end At

section RatFunc

/-- The pole-deleted product `F_{K,r}` is a nonzero rational function. -/
theorem poleDeletedProduct_ne_zero (K : ℕ) (r : ℤ) : poleDeletedProduct K r ≠ 0 := by
  rw [poleDeletedProduct]
  refine div_ne_zero ?_ ?_
  · simp [K.factorial_ne_zero]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (intPoleProduct_ne_zero _ _)

/-- `F_{K,r} ∏_{s ∈ R_K \ {r}} (x - s) = (K!)²` in `ℚ(x)`. -/
theorem poleDeletedProduct_mul_den (K : ℕ) (r : ℤ) :
    poleDeletedProduct K r * algebraMap ℚ[X] (RatFunc ℚ) (poleDeletedDen ℚ K r) =
      RatFunc.C ((K ! : ℚ) ^ 2) := by
  rw [poleDeletedProduct, div_mul_cancel₀]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (intPoleProduct_ne_zero _ _)

/-- Evaluating the rational function `F_{K,r}` along a ring hom `f : ℚ →+* F` at a point `x`
where the denominator does not vanish gives `poleDeletedProductAt K r x`. -/
theorem eval_poleDeletedProduct {F : Type} [Field F] (f : ℚ →+* F) {K : ℕ} {r : ℤ} {x : F}
    (hx : ∀ s ∈ (puncturedIcc K).erase r, x ≠ s) :
    (poleDeletedProduct K r).eval f x = poleDeletedProductAt K r x := by
  have hD : (poleDeletedDen F K r).eval x ≠ 0 := (eval_intPoleProduct_ne_zero_iff _ _).2 hx
  have hD' : (poleDeletedDen ℚ K r).eval₂ f x ≠ 0 := by
    rwa [← eval_map, map_intPoleProduct]
  have hden : (RatFunc.denom (poleDeletedProduct K r)).eval₂ f x ≠ 0 := by
    intro h
    refine hD' (eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f x ?_ h)
    rw [poleDeletedProduct, ← RatFunc.algebraMap_C]
    exact RatFunc.denom_div_dvd _ _
  have key := congrArg (RatFunc.eval f x) (poleDeletedProduct_mul_den K r)
  rw [RatFunc.eval_mul f x hden (by simp), RatFunc.eval_algebraMap, RatFunc.eval_C,
    Algebra.algebraMap_self, RingHom.id_apply, ← eq_div_iff hD'] at key
  rw [key, poleDeletedProductAt_def, ← eval_map, map_intPoleProduct]
  simp

end RatFunc

end Zeta5Irr
