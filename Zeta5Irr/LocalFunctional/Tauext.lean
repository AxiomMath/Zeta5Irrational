/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Zeta5Irr.LocalFunctional.BT
public import Zeta5Irr.LocalFunctional.ReflectIndex
public import Zeta5Irr.LocalFunctional.TauAn
public import Mathlib.NumberTheory.Padics.LocalField

/-!
# The extended functional `τ_Y^ext` on `𝓑_R`

For a finite set `R ⊆ ℤ` and a polynomial `Y ∈ ℚ_p[X]`, the extended functional on the space
`𝓑_R = ℚ_p⟨z⟩ ⊕ ⨁_{r ∈ R} ℚ_p` of near-pole decompositions is
`τ_Y^ext(f, (c_r)_{r ∈ R}) = τ^an(f) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - Y) ∈ ℚ_p[X]`,
where `τ^an` is the analytic functional, `H_j^{(5)}` the harmonic sum of order five and `d(r)`
the reflected index. It extends the functional `τ_Y` to functions with simple poles at the
integers of `R`: the pole `c_r / (z - r)` contributes `c_r (H_{d(r)}^{(5)} - Y)`.

## Main definitions

* `Zeta5Irr.tauExt R Y x`: the value `τ_Y^ext(x) ∈ ℚ_p[X]` for `x ∈ 𝓑_R`.

## Main results

* `Zeta5Irr.tauExt_mk`: `τ_Y^ext(f, (c_r)) = τ^an(f) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - Y)`.
* `Zeta5Irr.tauExt_smul`: `τ_Y^ext(a • x) = a • τ_Y^ext(x)` for `a ∈ ℚ_p`.

## Implementation notes

* `τ_Y^ext` is a function rather than a `ℚ_p`-linear map. Its analytic term `τ^an` takes the
  junk value `0` on non-convergent series, so it is additive only once every series
  `∑ f_d κ_d` converges, which the source proves for `p ≥ 5`. Homogeneity holds for every prime
  and is `Zeta5Irr.tauExt_smul`.
* The scalars `τ^an(f)` and `H_{d(r)}^{(5)} ∈ ℚ` are embedded in `ℚ_p[X]` as constant
  polynomials, and the sum over `r ∈ R` is a sum over the finite type `R`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The extended functional `τ_Y^ext : 𝓑_R → ℚ_p[X]`,
`τ_Y^ext(f, (c_r)_{r ∈ R}) = τ^an(f) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - Y)`. -/
@[zeta5irr "def_tauext"]
noncomputable def tauExt (R : Finset ℤ) (Y : Polynomial ℚ_[p]) (x : BT p R) :
    Polynomial ℚ_[p] :=
  Polynomial.C (tauAn (x.fst : ℚ_[p]⟦X⟧)) +
    ∑ r : R, x.res r • (Polynomial.C ((harmonicFive (reflectIndex r) : ℚ) : ℚ_[p]) - Y)

variable {R : Finset ℤ} (Y : Polynomial ℚ_[p])

/-- `τ_Y^ext(f, (c_r)) = τ^an(f) + ∑_{r ∈ R} c_r (H_{d(r)}^{(5)} - Y)`. -/
theorem tauExt_mk (f : tateAlgebra p) (c : R → ℚ_[p]) :
    tauExt R Y (BT.mk f c) = Polynomial.C (tauAn (f : ℚ_[p]⟦X⟧)) +
      ∑ r : R, c r • (Polynomial.C ((harmonicFive (reflectIndex r) : ℚ) : ℚ_[p]) - Y) :=
  rfl

/-- `τ^an` is `ℚ_p`-homogeneous: `τ^an(a • f) = a • τ^an(f)`. -/
theorem tauAn_smul (a : ℚ_[p]) (f : ℚ_[p]⟦X⟧) : tauAn (a • f) = a * tauAn f := by
  simp only [tauAn, PowerSeries.coeff_smul, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

/-- `τ_Y^ext` is `ℚ_p`-homogeneous: `τ_Y^ext(a • x) = a • τ_Y^ext(x)`. -/
theorem tauExt_smul (a : ℚ_[p]) (x : BT p R) : tauExt R Y (a • x) = a • tauExt R Y x := by
  simp only [tauExt, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  rw [Polynomial.smul_C, smul_eq_mul, ← tauAn_smul]
  rfl

/-- `τ_Y^ext(0) = 0`. -/
@[simp]
theorem tauExt_zero : tauExt R Y 0 = 0 := by
  simpa using tauExt_smul Y (0 : ℚ_[p]) 0

end Zeta5Irr
