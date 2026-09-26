/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Kappa
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# The analytic functional `τ^an` on the Tate algebra

For `f = ∑_{d ≥ 0} f_d z^d` in the Tate algebra `𝒜 = ℚ_p⟨z⟩`, the analytic functional is
`τ^an(f) = ∑_{d ≥ 0} f_d κ_d ∈ ℚ_p`, the sum of the series in `ℚ_p` when it converges and `0`
otherwise. Here `κ_d` are the weights `κ_d = d (d - 1) (d - 2) B_{d-3} / 24`.

## Main definitions

* `Zeta5Irr.tauAn f`: the value `∑_d f_d κ_d ∈ ℚ_p` (or `0` if the series does not converge).

## Main results

* `Zeta5Irr.tauAn_def`: `τ^an(f) = ∑' d, f_d κ_d`.
* `Zeta5Irr.hasSum_tauAn`: if the series converges, its sum is `τ^an(f)`.
* `Zeta5Irr.tauAn_of_not_summable`: if the series does not converge, `τ^an(f) = 0`.
* `Zeta5Irr.tauAn_coe_polynomial`: for a polynomial `U`, `τ^an(U) = ∑_{d} U_d κ_d`,
  a finite sum.

## Implementation notes

* `tauAn` is defined on all of `ℚ_[p]⟦X⟧` rather than only on `ℚ_p⟨z⟩`; its restriction to
  `ℚ_p⟨z⟩` is the functional of the source. This avoids coercions from the subalgebra.
* The convention "`0` when the series does not converge" is exactly the junk value of `tsum`.
  Summation is unconditional convergence in `ℚ_p`, which for a non-archimedean field agrees
  with convergence of the partial sums whenever the terms tend to `0`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The analytic functional `τ^an(f) = ∑_{d ≥ 0} f_d κ_d ∈ ℚ_p` on power series over `ℚ_p`,
with value `0` when the series does not converge. On the Tate algebra `ℚ_p⟨z⟩` this is the
functional `τ^an : 𝒜 → ℚ_p`. -/
@[zeta5irr "def_tau_an"]
noncomputable def tauAn (f : ℚ_[p]⟦X⟧) : ℚ_[p] :=
  ∑' d, coeff d f * (kappa d : ℚ_[p])

/-- `τ^an(f) = ∑' d, f_d κ_d`. -/
theorem tauAn_def (f : ℚ_[p]⟦X⟧) : tauAn f = ∑' d, coeff d f * (kappa d : ℚ_[p]) :=
  rfl

/-- If the series `∑ f_d κ_d` converges, then its sum is `τ^an(f)`. -/
@[zeta5irr "def_tau_an"]
theorem hasSum_tauAn {f : ℚ_[p]⟦X⟧} (hf : Summable fun d => coeff d f * (kappa d : ℚ_[p])) :
    HasSum (fun d => coeff d f * (kappa d : ℚ_[p])) (tauAn f) :=
  hf.hasSum

/-- If the series `∑ f_d κ_d` has sum `a`, then `τ^an(f) = a`. -/
theorem tauAn_eq_of_hasSum {f : ℚ_[p]⟦X⟧} {a : ℚ_[p]}
    (h : HasSum (fun d => coeff d f * (kappa d : ℚ_[p])) a) : tauAn f = a :=
  h.tsum_eq

/-- If the series `∑ f_d κ_d` does not converge, then `τ^an(f) = 0`. -/
@[zeta5irr "def_tau_an"]
theorem tauAn_of_not_summable {f : ℚ_[p]⟦X⟧}
    (hf : ¬Summable fun d => coeff d f * (kappa d : ℚ_[p])) : tauAn f = 0 :=
  tsum_eq_zero_of_not_summable hf

/-- `τ^an(0) = 0`. -/
@[simp]
theorem tauAn_zero : tauAn (0 : ℚ_[p]⟦X⟧) = 0 := by
  simp [tauAn]

/-- For a polynomial `U ∈ ℚ_p[z]`, `τ^an(U) = ∑_{d ∈ supp U} U_d κ_d`, a finite sum. -/
theorem tauAn_coe_polynomial (U : Polynomial ℚ_[p]) :
    tauAn (U : ℚ_[p]⟦X⟧) = ∑ d ∈ U.support, U.coeff d * (kappa d : ℚ_[p]) := by
  rw [tauAn, tsum_eq_sum (s := U.support)]
  · simp
  · intro d hd
    simp [Polynomial.notMem_support_iff.mp hd]

end Zeta5Irr
