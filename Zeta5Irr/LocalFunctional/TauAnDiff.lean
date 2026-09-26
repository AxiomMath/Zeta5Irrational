/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauAnReflect
public import Zeta5Irr.LocalFunctional.TauDiffPoly

/-!
# The difference identity for `τ^an`

Let `p ≥ 5` be a prime and `f ∈ 𝒜 = ℚ_p⟨z⟩`. Then `τ^an(f(z + 1)) - τ^an(f(z)) = f_4`, the
coefficient of `z ^ 4` in `f`.

By the expansion of `τ^an` of an affine substitution, `τ^an(f(1 + z)) = ∑_d f_d τ^an((1 + z)^d)`.
The polynomial `(1 + z)^d` has rational coefficients, so
`τ^an((1 + z)^d) = τ((x + 1)^d) = τ(x^d) + [x^4] x^d = κ_d + [d = 4]` by the difference identity
for `τ`. Hence the series is `∑_d f_d κ_d + f_4 = τ^an(f) + f_4`.

## Main results

* `Zeta5Irr.tauAn_tateSubst_one_one_sub`: `τ^an(f(1 + z)) - τ^an(f) = f_4`.

## Implementation notes

The source reduces to monomials by linearity and continuity of the three functionals involved.
Here the reduction is instead made through the termwise expansion
`τ^an(f(u + cz)) = ∑_d f_d τ^an((u + cz)^d)`, established for the reflection identity by
exchanging the order of an unconditionally summable double series in `ℚ_p`. The monomial case is
the same as in the source.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- `τ^an((1 + z)^d) = κ_d + [d = 4]`: the difference identity for `τ` on the monomial `x^d`. -/
theorem tauAn_one_add_X_pow (d : ℕ) :
    tauAn ((C (1 : ℚ_[p]) + C 1 * X) ^ d) = (kappa d : ℚ_[p]) + if 4 = d then 1 else 0 := by
  have h : (C (1 : ℚ_[p]) + C 1 * X) ^ d =
      ((((Polynomial.X ^ d : Polynomial ℚ).comp (Polynomial.X + 1)).map
        (algebraMap ℚ ℚ_[p]) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
    simp [add_comm]
  have h2 := tau_comp_X_add_one_sub (Polynomial.X ^ d : Polynomial ℚ)
  rw [tau_X_pow_eq_kappa, Polynomial.coeff_X_pow, sub_eq_iff_eq_add'] at h2
  rw [h, tauAn_map_eq_tau, h2]
  split_ifs <;> simp

/-- **The difference identity for `τ^an`.** For a prime `p ≥ 5` and `f ∈ ℚ_p⟨z⟩`,
`τ^an(f(z + 1)) - τ^an(f(z))` is the coefficient of `z ^ 4` in `f`. -/
@[zeta5irr "lem_tau_an_diff"]
theorem tauAn_tateSubst_one_one_sub (hp5 : 5 ≤ p) {f : ℚ_[p]⟦X⟧}
    (hf : f ∈ tateAlgebra p) : tauAn (tateSubst 1 1 f) - tauAn f = coeff 4 f := by
  have hterm : ∀ d, coeff d f * tauAn ((C (1 : ℚ_[p]) + C 1 * X) ^ d) =
      coeff d f * (kappa d : ℚ_[p]) + Pi.single (M := fun _ => ℚ_[p]) 4 (coeff 4 f) d := by
    intro d
    rw [tauAn_one_add_X_pow]
    rcases eq_or_ne d 4 with rfl | hd
    · simp [mul_add]
    · simp [hd, Ne.symm hd]
  rw [tauAn_tateSubst hp5 hf (by simp) (by simp), tsum_congr hterm,
    Summable.tsum_add (hasSum_coeff_mul_kappa_tauAn hp5 hf).summable
      (hasSum_pi_single (4 : ℕ) (coeff 4 f)).summable,
    (hasSum_coeff_mul_kappa_tauAn hp5 hf).tsum_eq, (hasSum_pi_single (4 : ℕ) (coeff 4 f)).tsum_eq]
  ring

end Zeta5Irr
