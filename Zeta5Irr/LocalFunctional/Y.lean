/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Cp

/-!
# The linear polynomial `Y_p`

For a prime `p`, the polynomial `Y_p = p^5 X + C_p ∈ ℚ_p[X]` is the affine change of variable
used in the distribution argument; here `C_p` is the constant
`C_p = ∑_{a=1}^{p-1} τ^an(ε_{-a/p})`.

## Main definitions

* `Zeta5Irr.Yp p`: the polynomial `Y_p = p^5 X + C_p`.

## Main results

* `Zeta5Irr.coeff_Yp_zero`, `Zeta5Irr.coeff_Yp_one`: the coefficients of `Y_p`.
* `Zeta5Irr.natDegree_Yp`, `Zeta5Irr.degree_Yp`: `Y_p` has degree `1`.
* `Zeta5Irr.leadingCoeff_Yp`: the leading coefficient of `Y_p` is `p^5`.
* `Zeta5Irr.eval_Yp`: `Y_p(x) = p^5 x + C_p`.

## Implementation notes

The blueprint writes the linear term as `p^5 X`; it is stated here as `C (p^5) * X`, which is
equal to `p^5 • X` and matches the normal form of Mathlib's linear-polynomial lemmas
(`Polynomial.degree_linear` and friends).

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The polynomial `Y_p = p^5 X + C_p ∈ ℚ_p[X]`. -/
@[zeta5irr "def_Y"]
noncomputable def Yp : ℚ_[p][X] :=
  C ((p : ℚ_[p]) ^ 5) * X + C (Cp p)

/-- The constant coefficient of `Y_p` is `C_p`. -/
theorem coeff_Yp_zero : (Yp p).coeff 0 = Cp p := by
  simp [Yp]

/-- The linear coefficient of `Y_p` is `p^5`. -/
theorem coeff_Yp_one : (Yp p).coeff 1 = (p : ℚ_[p]) ^ 5 := by
  rw [Yp, coeff_add, coeff_C_mul_X, coeff_C]
  simp

/-- The coefficients of `Y_p` in degree at least `2` vanish. -/
theorem coeff_Yp_of_two_le {n : ℕ} (hn : 2 ≤ n) : (Yp p).coeff n = 0 := by
  rw [Yp, coeff_add, coeff_C_mul_X, coeff_C]
  simp [show n ≠ 1 by omega, show n ≠ 0 by omega]

/-- Evaluating `Y_p` at `x` gives `p^5 x + C_p`. -/
theorem eval_Yp (x : ℚ_[p]) : (Yp p).eval x = (p : ℚ_[p]) ^ 5 * x + Cp p := by
  simp [Yp]

private theorem prime_pow_five_ne_zero : ((p : ℚ_[p]) ^ 5) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- `Y_p` has degree `1`. -/
theorem degree_Yp : (Yp p).degree = 1 :=
  degree_linear (prime_pow_five_ne_zero p)

/-- `Y_p` has natural degree `1`. -/
theorem natDegree_Yp : (Yp p).natDegree = 1 :=
  natDegree_linear (prime_pow_five_ne_zero p)

/-- The leading coefficient of `Y_p` is `p^5`. -/
theorem leadingCoeff_Yp : (Yp p).leadingCoeff = (p : ℚ_[p]) ^ 5 :=
  leadingCoeff_linear (prime_pow_five_ne_zero p)

end Zeta5Irr
