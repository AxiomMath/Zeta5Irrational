/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG

/-!
# The Gauss valuation of a scalar multiple

Let `p` be a prime. For a nonzero rational `c` and a rational polynomial `A`, the Gauss
valuation of `c A` (viewed in `ℚ_p[X]`) is `v_p(c) + v_p^G(A)`: the coefficients of `c A` are
`c` times those of `A`, so each of their `p`-adic valuations shifts by `v_p(c)`, and hence so
does their minimum.

## Main results

* `Zeta5Irr.vpG_map_smul`: `v_p^G(c A) = v_p(c) + v_p^G(A)` for `c ∈ ℚ ∖ {0}`, `A ∈ ℚ[X]`.

## Implementation notes

* A rational polynomial `A` is regarded as an element of `ℚ_p[X]` via
  `A.map (Rat.castHom ℚ_[p])`, which is how `v_p^G` is applied to it.
* The blueprint assumes `A ≠ 0`; the identity also holds for `A = 0`, where both sides are
  `+∞`, so that hypothesis is dropped. The hypothesis `c ≠ 0` is needed, since `v_p(0)` is
  the junk value `0` for `padicValRat`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §8.1 (The normalizing factor and integrality).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- For a nonzero rational `c` and `A ∈ ℚ[X]`, `v_p^G(c A) = v_p(c) + v_p^G(A)`, where the
rational polynomials are viewed in `ℚ_p[X]`. -/
@[zeta5irr "lem_norm_vpG_smul"]
theorem vpG_map_smul {c : ℚ} (hc : c ≠ 0) (A : ℚ[X]) :
    vpG ((c • A).map (Rat.castHom ℚ_[p])) =
      (padicValRat p c : WithTop ℤ) + vpG (A.map (Rat.castHom ℚ_[p])) := by
  rw [Polynomial.map_smul, smul_eq_C_mul, vpG, gaussAddVal_C_mul, Rat.coe_castHom,
    Padic.addValuation.apply (by exact_mod_cast hc), Padic.valuation_ratCast]

end Zeta5Irr
