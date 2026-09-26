/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauAn
public import Zeta5Irr.LocalFunctional.TauFar

/-!
# The $p$-adic constant `C_p`

For a prime `p`, the constant
`C_p = ∑_{a=1}^{p-1} τ^an(ε_{-a/p}) ∈ ℚ_p`
is the sum of the analytic functional `τ^an` over the far-pole power series `ε_{-a/p}`. The
definition makes sense because `v_p(-a/p) = -1 < 0` for `1 ≤ a ≤ p - 1`, so each `ε_{-a/p}`
lies in the Tate algebra.

## Main definitions

* `Zeta5Irr.Cp p`: the constant `C_p = ∑_{a=1}^{p-1} τ^an(ε_{-a/p})`.

## Main results

* `Zeta5Irr.valuation_intCast_div_prime`, `Zeta5Irr.norm_intCast_div_prime`: `v_p(m/p) = -1`,
  i.e. `|m/p|_p = p`, when `p ∤ m`; for `m = -a` with `1 ≤ a ≤ p - 1` these are the poles of
  `C_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

variable (p : ℕ) [Fact p.Prime]

/-- The $p$-adic constant `C_p = ∑_{a=1}^{p-1} τ^an(ε_{-a/p}) ∈ ℚ_p`. -/
@[zeta5irr "def_Cp"]
noncomputable def Cp : ℚ_[p] :=
  ∑ a ∈ Finset.Ico 1 p, tauAn (farEps (-((a : ℚ_[p]) / p)))

variable {p}

/-- If `p ∤ m` then `v_p(m/p) = -1`; in particular the pole `m / p` is far from the origin.
For `m = -a` with `1 ≤ a ≤ p - 1` these are the poles appearing in `C_p`. -/
theorem valuation_intCast_div_prime {m : ℤ} (h : ¬(p : ℤ) ∣ m) :
    ((m : ℚ_[p]) / (p : ℚ_[p])).valuation = -1 := by
  have hm : (m : ℚ) ≠ 0 := by rintro hm; exact h (by simp_all)
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [show ((m : ℚ_[p]) / (p : ℚ_[p])) = (((m : ℚ) / p : ℚ) : ℚ_[p]) by push_cast; rfl,
    Padic.valuation_ratCast, padicValRat.div hm hp, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd h, padicValRat.self (Fact.out : p.Prime).one_lt]
  simp

/-- If `p ∤ m` then `|m/p|_p = p`. -/
theorem norm_intCast_div_prime {m : ℤ} (h : ¬(p : ℤ) ∣ m) : ‖(m : ℚ_[p]) / p‖ = p := by
  have h1 : ‖(m : ℚ_[p])‖ = 1 := le_antisymm (Padic.norm_int_le_one _)
    (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))
  rw [norm_div, h1, Padic.norm_p, one_div, inv_inv]

end Zeta5Irr
