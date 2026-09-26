/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Kappa
public import Zeta5Irr.LocalFunctional.Tau

/-!
# The functional `τ` on monomials

The functional `τ(P) = L(P''') / 24` takes the value `κ_d` on the monomial `x ^ d`, for every
`d ≥ 0`. For `d ≤ 2` both sides vanish, since `(x ^ d)''' = 0`; for `d ≥ 3` the third derivative
is `d (d - 1) (d - 2) x ^ (d - 3)`, which `L` sends to `d (d - 1) (d - 2) B_{d-3}`.

## Main results

* `Zeta5Irr.tau_X_pow_eq_kappa`: `τ (X ^ d) = κ_d` for every `d : ℕ`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §3 (the functional `τ_X`).
-/

@[expose] public section

namespace Zeta5Irr

open scoped Polynomial
open Polynomial (X)

/-- For every `d ≥ 0`, `τ (X ^ d) = κ_d`. -/
@[zeta5irr "lem_tau_monomial"]
theorem tau_X_pow_eq_kappa (d : ℕ) : tau (X ^ d) = kappa d := by
  rw [tau_X_pow, kappa]

end Zeta5Irr
