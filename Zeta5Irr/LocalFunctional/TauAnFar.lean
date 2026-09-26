/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauFarMem
public import Zeta5Irr.LocalFunctional.TauAnConv
public import Mathlib.NumberTheory.Padics.LocalField

/-!
# The analytic functional on a far pole

Let `p ≥ 5` be a prime and `s ∈ ℚ_p` with `v_p(s) < 0`. Then
`τ^an(ε_s) = -(1/4) ∑_{k ≥ 0} binom(k+3, 3) B_k s^{-k-4}`, the series converging in `ℚ_p`.

Indeed `ε_s ∈ 𝒜` has `k`-th coefficient `-s^{-k-1}`, so `τ^an(ε_s) = -∑_k s^{-k-1} κ_k`. The
terms with `k ≤ 2` vanish, and after reindexing `k = m + 3` one uses
`κ_{m+3} = (m+3)(m+2)(m+1) B_m / 24 = binom(m+3, 3) B_m / 4`.

## Main results

* `Zeta5Irr.hasSum_tauAn_farEps`: the series `∑_k -(1/4) binom(k+3, 3) B_k s^{-k-4}` has sum
  `τ^an(ε_s)`.
* `Zeta5Irr.tauAn_farEps`: the statement of the source: the series
  `∑_k binom(k+3, 3) B_k s^{-k-4}` converges and `τ^an(ε_s) = -(1/4)` times its sum.

## Implementation notes

* `s^{-k-4}` is written `(s⁻¹) ^ (k + 4)`, matching the coefficients of `Zeta5Irr.farEps`.
* Convergence is unconditional convergence (`Summable`) in `ℚ_p`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Finset

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p ≥ 5` and `v_p(s) < 0`, the series
`∑_{k ≥ 0} -(1/4) binom(k+3, 3) B_k s^{-k-4}` has sum `τ^an(ε_s)`. -/
theorem hasSum_tauAn_farEps (hp5 : 5 ≤ p) {s : ℚ_[p]} (hs : s.valuation < 0) :
    HasSum (fun k : ℕ => -(1 / 4) *
      (((k + 3).choose 3 : ℚ_[p]) * (bernoulli k : ℚ_[p]) * (s⁻¹) ^ (k + 4)))
      (tauAn (farEps s)) := by
  have h := hasSum_coeff_mul_kappa_tauAn hp5 (farEps_mem_tateAlgebra_and_tateNorm hs).1
  rw [← hasSum_nat_add_iff' 3] at h
  have h0 : ∑ i ∈ range 3, coeff i (farEps s) * (kappa i : ℚ_[p]) = 0 := by
    simp [sum_range_succ]
  rw [h0, sub_zero] at h
  convert h using 2 with k
  rw [coeff_farEps, kappa, Nat.add_sub_cancel, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  simp only [Nat.factorial, Nat.succ_eq_add_one]
  push_cast
  ring

/-- **`τ^an` on a far pole.** For a prime `p ≥ 5` and `s ∈ ℚ_p` with `v_p(s) < 0`, the series
`∑_{k ≥ 0} binom(k+3, 3) B_k s^{-k-4}` converges in `ℚ_p`, and
`τ^an(ε_s) = -(1/4) ∑_{k ≥ 0} binom(k+3, 3) B_k s^{-k-4}`. -/
@[zeta5irr "lem_tau_an_far"]
theorem tauAn_farEps (hp5 : 5 ≤ p) {s : ℚ_[p]} (hs : s.valuation < 0) :
    Summable (fun k : ℕ => ((k + 3).choose 3 : ℚ_[p]) * (bernoulli k : ℚ_[p]) * (s⁻¹) ^ (k + 4))
      ∧ tauAn (farEps s) = -(1 / 4) *
        ∑' k : ℕ, ((k + 3).choose 3 : ℚ_[p]) * (bernoulli k : ℚ_[p]) * (s⁻¹) ^ (k + 4) := by
  have h := hasSum_tauAn_farEps hp5 hs
  have h' : HasSum
      (fun k : ℕ => ((k + 3).choose 3 : ℚ_[p]) * (bernoulli k : ℚ_[p]) * (s⁻¹) ^ (k + 4))
      (-4 * tauAn (farEps s)) := by
    convert h.mul_left (-4) using 2 with k
    ring
  exact ⟨h'.summable, by rw [h'.tsum_eq]; ring⟩

end Zeta5Irr
