/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.Parameters.Defs
public import Zeta5Irr.LocalFunctional.ReflectIndex
public import Zeta5Irr.LocalFunctional.Y

/-!
# The local pole value `w_p(m)`

For a prime `p` and an integer `m`, the local pole value is the polynomial
`w_p(m) ∈ ℚ_p[X]` given by
* `w_p(m) = H_{d(m/p)}^{(5)} - Y_p` if `p ∣ m`, where `m / p ∈ ℤ` and `d` is the reflected
  index;
* `w_p(m) = τ^an(ε_{m/p})` if `p ∤ m`, a constant polynomial; here `m / p ∈ ℚ_p` has
  valuation `v_p(m/p) = -1 < 0`, so `ε_{m/p}` is the far-pole power series.

It is the value contributed by the single pole `m / p` to the distributed functional.

## Main definitions

* `Zeta5Irr.localPoleValue p m`: the local pole value `w_p(m) ∈ ℚ_p[X]`.

## Main results

* `Zeta5Irr.localPoleValue_of_dvd`, `Zeta5Irr.localPoleValue_of_not_dvd`: the two cases of
  the definition.
* `Zeta5Irr.localPoleValue_mul_left`: `w_p(pρ) = H_{d(ρ)}^{(5)} - Y_p` for `ρ ∈ ℤ`.
* `Zeta5Irr.localPoleValue_zero`: `w_p(0) = -Y_p`.

## Implementation notes

* The value is a polynomial in `ℚ_p[X]` in both cases, the second case being the constant
  polynomial `C (τ^an(ε_{m/p}))`, so that both cases share the codomain of `Y_p`.
* In the first case `m / p` is the exact integer quotient `m / (p : ℤ)`; in the second it is
  the quotient `(m : ℚ_p) / p` in `ℚ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The local pole value `w_p(m) ∈ ℚ_p[X]`: `H_{d(m/p)}^{(5)} - Y_p` if `p ∣ m`, and the
constant `τ^an(ε_{m/p})` if `p ∤ m`. -/
@[zeta5irr "def_tau_distval"]
noncomputable def localPoleValue (m : ℤ) : ℚ_[p][X] :=
  if (p : ℤ) ∣ m then C ((harmonicFive (reflectIndex (m / p)) : ℚ) : ℚ_[p]) - Yp p
  else C (tauAn (farEps ((m : ℚ_[p]) / (p : ℚ_[p]))))

variable {p}

/-- The case `p ∣ m` of the local pole value: `w_p(m) = H_{d(m/p)}^{(5)} - Y_p`. -/
theorem localPoleValue_of_dvd {m : ℤ} (h : (p : ℤ) ∣ m) :
    localPoleValue p m = C ((harmonicFive (reflectIndex (m / p)) : ℚ) : ℚ_[p]) - Yp p :=
  by simp [localPoleValue, h]

/-- The case `p ∤ m` of the local pole value: `w_p(m) = τ^an(ε_{m/p})`. -/
theorem localPoleValue_of_not_dvd {m : ℤ} (h : ¬(p : ℤ) ∣ m) :
    localPoleValue p m = C (tauAn (farEps ((m : ℚ_[p]) / (p : ℚ_[p])))) :=
  by simp [localPoleValue, h]

/-- `w_p(pρ) = H_{d(ρ)}^{(5)} - Y_p` for every integer `ρ`. -/
theorem localPoleValue_mul_left (ρ : ℤ) :
    localPoleValue p (p * ρ) = C ((harmonicFive (reflectIndex ρ) : ℚ) : ℚ_[p]) - Yp p := by
  rw [localPoleValue_of_dvd (dvd_mul_right _ _),
    Int.mul_ediv_cancel_left _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]

/-- `w_p(0) = -Y_p`. -/
@[simp]
theorem localPoleValue_zero : localPoleValue p 0 = -Yp p := by
  simpa [show reflectIndex 0 = 0 from rfl, harmonicFive_zero] using
    localPoleValue_mul_left (p := p) 0

end Zeta5Irr
