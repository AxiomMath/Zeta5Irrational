/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.BT
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The near-pole decomposition `δ_R` of a polynomial

Let `R ⊆ ℤ` be finite, `E_R = ∏_{r ∈ R} (z - r)`, and `U ∈ ℚ_p[z]`. Euclidean division by the
monic polynomial `E_R` writes `U = P E_R + B` with `P, B ∈ ℚ_p[z]` and `deg B < #R`, the
quotient `P` being unique. The near-pole decomposition of `U` is
`δ_R(U) = (P, (U(r) / E_R'(r))_{r ∈ R}) ∈ 𝓑_R`: the quotient, viewed in the Tate algebra
`ℚ_p⟨z⟩`, together with the residues at `r ∈ R` of the partial fraction expansion of
`B / E_R = ∑_{r ∈ R} (U(r) / E_R'(r)) / (z - r)`.

## Main definitions

* `Zeta5Irr.tateAlgebra.ofPolynomial`: the inclusion `ℚ_p[z] → ℚ_p⟨z⟩` as a `ℚ_p`-algebra
  homomorphism.
* `Zeta5Irr.deltaR R U`: the near-pole decomposition `δ_R(U) ∈ 𝓑_R`.

## Main results

* `Zeta5Irr.deltaR_fst`, `Zeta5Irr.deltaR_res`: the two components of `δ_R(U)`.
* `Zeta5Irr.deltaR_fst_eq_of_eq_mul_add`: if `U = P E_R + B` with `deg B < #R`, then the
  Tate-algebra component of `δ_R(U)` is `P`.
* `Zeta5Irr.deltaR_add`, `Zeta5Irr.deltaR_smul`: `δ_R` is `ℚ_p`-linear.

## Implementation notes

The quotient `P` is `U /ₘ E_R` (`Polynomial.divByMonic`), which makes sense since `E_R` is
monic, and the remainder `B` is `U %ₘ E_R`; the defining property of the source's
decomposition is `Zeta5Irr.deltaR_fst_eq_of_eq_mul_add`. The residue at `r` is the value
`U(r) / E_R'(r)`; since the elements of `R` are distinct, `E_R'(r) ≠ 0`, but the definition
does not depend on this.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

namespace tateAlgebra

variable (p) in
/-- The inclusion `ℚ_p[z] → ℚ_p⟨z⟩` of polynomials into the Tate algebra, as a
`ℚ_p`-algebra homomorphism. -/
noncomputable def ofPolynomial : ℚ_[p][X] →ₐ[ℚ_[p]] tateAlgebra p :=
  (Polynomial.coeToPowerSeries.algHom ℚ_[p]).codRestrict (tateAlgebra p) coe_mem_tateAlgebra

/-- The image of `U ∈ ℚ_p[z]` in `ℚ_p⟨z⟩` is `U` viewed as a power series. -/
@[simp]
theorem coe_ofPolynomial (U : ℚ_[p][X]) :
    ((ofPolynomial p U : tateAlgebra p) : PowerSeries ℚ_[p]) = (U : PowerSeries ℚ_[p]) :=
  rfl

/-- The inclusion `ℚ_p[z] → ℚ_p⟨z⟩` is injective. -/
theorem ofPolynomial_injective : Function.Injective (ofPolynomial p) := fun U V h => by
  have := congrArg (fun f : tateAlgebra p => (f : PowerSeries ℚ_[p])) h
  simpa using this

end tateAlgebra

variable (R : Finset ℤ)

/-- The near-pole decomposition `δ_R(U) = (P, (U(r) / E_R'(r))_{r ∈ R}) ∈ 𝓑_R` of a
polynomial `U ∈ ℚ_p[z]`, where `U = P E_R + B` with `deg B < #R` is the Euclidean division
of `U` by `E_R = ∏_{r ∈ R} (z - r)`. -/
@[zeta5irr "def_tau_delta"]
noncomputable def deltaR (U : ℚ_[p][X]) : BT p R :=
  BT.mk (tateAlgebra.ofPolynomial p (U /ₘ intPoleProduct R ℚ_[p]))
    fun r => U.eval ((r : ℤ) : ℚ_[p]) /
      (derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p])

variable {R}

/-- The Tate-algebra component of `δ_R(U)` is the quotient `U /ₘ E_R`. -/
@[simp]
theorem deltaR_fst (U : ℚ_[p][X]) :
    (deltaR R U).fst = tateAlgebra.ofPolynomial p (U /ₘ intPoleProduct R ℚ_[p]) :=
  rfl

/-- The residue of `δ_R(U)` at `r ∈ R` is `U(r) / E_R'(r)`. -/
@[simp]
theorem deltaR_res (U : ℚ_[p][X]) (r : R) :
    (deltaR R U).res r = U.eval ((r : ℤ) : ℚ_[p]) /
      (derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p]) :=
  rfl

/-- The defining property of `δ_R`: if `U = P E_R + B` with `P, B ∈ ℚ_p[z]` and `deg B < #R`,
then `δ_R(U) = (P, (U(r) / E_R'(r))_{r ∈ R})`. -/
@[zeta5irr "def_tau_delta"]
theorem deltaR_eq_of_eq_mul_add {U P B : ℚ_[p][X]}
    (hU : U = P * intPoleProduct R ℚ_[p] + B) (hB : B.degree < R.card) :
    deltaR R U = BT.mk (tateAlgebra.ofPolynomial p P) fun r => U.eval ((r : ℤ) : ℚ_[p]) /
      (derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p]) := by
  rw [deltaR, divByMonic_intPoleProduct_eq_of_eq_mul_add R ℚ_[p] hU hB]

/-- If `U = P E_R + B` with `deg B < #R`, then the Tate-algebra component of `δ_R(U)` is
`P`. -/
theorem deltaR_fst_eq_of_eq_mul_add {U P B : ℚ_[p][X]}
    (hU : U = P * intPoleProduct R ℚ_[p] + B) (hB : B.degree < R.card) :
    (deltaR R U).fst = tateAlgebra.ofPolynomial p P := by
  rw [deltaR_eq_of_eq_mul_add hU hB, BT.fst_mk]

/-- `δ_R` is additive. -/
theorem deltaR_add (U V : ℚ_[p][X]) : deltaR R (U + V) = deltaR R U + deltaR R V := by
  have hq := Polynomial.add_divByMonic U V (q := intPoleProduct R ℚ_[p])
  refine BT.ext ?_ fun r => ?_
  · simpa [BT.fst, deltaR] using congrArg (tateAlgebra.ofPolynomial p) hq
  · simp [BT.res, deltaR, add_div]

/-- `δ_R` is `ℚ_p`-homogeneous. -/
theorem deltaR_smul (a : ℚ_[p]) (U : ℚ_[p][X]) : deltaR R (a • U) = a • deltaR R U := by
  have hq := Polynomial.smul_divByMonic a U (q := intPoleProduct R ℚ_[p])
  refine BT.ext ?_ fun r => ?_
  · simpa [BT.fst, deltaR] using congrArg (tateAlgebra.ofPolynomial p) hq
  · simp [BT.res, deltaR, mul_div_assoc]

end Zeta5Irr
