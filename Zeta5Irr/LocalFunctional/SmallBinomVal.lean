/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Qbinom
public import Zeta5Irr.LocalFunctional.SmallIntval

/-!
# Binomial polynomials map `ℤ_p` into `ℤ_p`

Let `p` be a prime and `k ≥ 0`. The binomial polynomial `(x choose k) ∈ ℚ[x]` takes integer
values at the integers, so its value at any `x ∈ ℤ_p` lies in `ℤ_p`.

## Main results

* `Zeta5Irr.norm_aeval_qbinom_le_one`: `‖(x choose k)‖_p ≤ 1` for every `x ∈ ℤ_p`.
* `Zeta5Irr.exists_padicInt_eq_aeval_qbinom`: `(x choose k)` is the image of a `p`-adic
  integer for every `x ∈ ℤ_p`.

## Implementation notes

As in `Zeta5Irr.norm_aeval_padicInt_le_one`, the value at `x ∈ ℤ_p` is
`Polynomial.aeval (x : ℚ_[p]) (qbinom k)`, and membership in `ℤ_p` is stated as `‖·‖ ≤ 1`,
the defining condition of the subtype `ℤ_[p]` of `ℚ_[p]`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.6 (small primes).
-/

@[expose] public section

open Polynomial

namespace Zeta5Irr

/-- The value of the binomial polynomial `(x choose k)` at a `p`-adic integer `x` lies in
`ℤ_p`: `‖(x choose k)‖_p ≤ 1`. -/
@[zeta5irr "lem_small_binom_val"]
theorem norm_aeval_qbinom_le_one {p : ℕ} [Fact p.Prime] (k : ℕ) (x : ℤ_[p]) :
    ‖aeval (x : ℚ_[p]) (qbinom k)‖ ≤ 1 :=
  norm_aeval_padicInt_le_one (fun m => ⟨_, eval_intCast_qbinom k m⟩) x

/-- The value of the binomial polynomial `(x choose k)` at a `p`-adic integer `x` is the image
of a `p`-adic integer. -/
theorem exists_padicInt_eq_aeval_qbinom {p : ℕ} [Fact p.Prime] (k : ℕ) (x : ℤ_[p]) :
    ∃ y : ℤ_[p], (y : ℚ_[p]) = aeval (x : ℚ_[p]) (qbinom k) :=
  ⟨⟨_, norm_aeval_qbinom_le_one k x⟩, rfl⟩

end Zeta5Irr
