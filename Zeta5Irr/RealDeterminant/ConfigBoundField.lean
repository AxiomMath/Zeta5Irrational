/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.RealDeterminant.ConfigBound
public import Zeta5Irr.Measure.RhoPotentialModified

/-!
# A bound for every configuration, with the external field

Let `t = (t_1, …, t_h) ∈ [0, ∞)^h` have pairwise distinct entries. Then
`2 ∑_{i < j} log |t_i - t_j| - K ∑_i V(t_i) + ∑_i √t_i`
`≤ (-1329 λ / 200 - I(ρ)) K² + (120 + √2) h + 2 h log K`,
where `V` is the external field, `ρ` the rational arcsine measure, `K = 40 n`, `h = 37 n`
and `λ = 37 / 40`.

This is the general configuration bound applied to `W(t) = V(t) - √t / K`,
`m = -1329/200 + √2 / K` (admissible by the modified potential inequality) and `ε = K⁻²`.

## Main results

* `Zeta5Irr.two_mul_sum_log_abs_sub_sub_externalField_add_sum_sqrt_le`: the bound above.

## Implementation notes

* The measure `ρ` lives on `ℝ`; its energy is that of its image `rho.map ((↑) : ℝ → ℂ)` on `ℂ`.
* The sum over `i < j` is written `∑ i, ∑ j ∈ Finset.Ioi i`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §10.2 (A bound for every configuration).
-/

@[expose] public section

open Real

namespace Zeta5Irr

/-- **A bound for every configuration, with the external field** (Fauzan, §10.2). For
`t = (t_1, …, t_h) ∈ [0, ∞)^h` with pairwise distinct entries,
`2 ∑_{i < j} log |t_i - t_j| - K ∑_i V(t_i) + ∑_i √t_i`
`≤ (-1329 λ / 200 - I(ρ)) K² + (120 + √2) h + 2 h log K`,
where `K = 40 n`, `h = 37 n` and `λ = 37 / 40`. -/
@[zeta5irr "lem_config_bound_field"]
theorem two_mul_sum_log_abs_sub_sub_externalField_add_sum_sqrt_le {n : ℕ} (hn : 0 < n)
    {t : Fin (matrixOrder n) → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht : Function.Injective t) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, log |t i - t j| - poleBound n * ∑ i, externalField (t i) +
        ∑ i, √(t i) ≤
      (-1329 * (orderRatio : ℝ) / 200 - logEnergy (rho.map ((↑) : ℝ → ℂ))) *
          (poleBound n : ℝ) ^ 2 +
        (120 + √2) * matrixOrder n + 2 * matrixOrder n * log (poleBound n) := by
  set K : ℕ := poleBound n with hKdef
  have hK2 : 2 ≤ K := by simp only [hKdef, poleBound]; omega
  have hK : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hε : (0 : ℝ) < ((K : ℝ) ^ 2)⁻¹ := by positivity
  have key := two_mul_sum_log_abs_sub_sub_le hn hε ht0 ht (fun x => externalField x - √x / K)
    ((potentialBound : ℝ) + √2 / K) (fun x hx => by
      have := two_mul_logPotential_rho_sub_externalField_add_sqrt_div_le hK2 hx
      linarith)
  have hsq : √(((K : ℝ) ^ 2)⁻¹) = (K : ℝ)⁻¹ := by
    rw [sqrt_inv, sqrt_sq hK.le]
  have hlog : log (((K : ℝ) ^ 2)⁻¹) = -(2 * log K) := by
    rw [log_inv, log_pow]; push_cast; ring
  have hsum : ∑ i, (externalField (t i) - √(t i) / K) =
      ∑ i, externalField (t i) - (K : ℝ)⁻¹ * ∑ i, √(t i) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsq, hlog, hsum] at key
  have hh : (matrixOrder n : ℝ) = (orderRatio : ℝ) * K := by
    simp only [hKdef, matrixOrder, poleBound, orderRatio]; push_cast; ring
  have hM : (potentialBound : ℝ) = -1329 / 200 := by norm_num [potentialBound]
  rw [hM] at key
  have hKinv : (K : ℝ) * (K : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hK.ne'
  have e1 : (orderRatio : ℝ) * (-1329 / 200 + √2 / K) * (K : ℝ) ^ 2 =
      -1329 * (orderRatio : ℝ) / 200 * (K : ℝ) ^ 2 + √2 * matrixOrder n := by
    rw [hh]; field_simp
  have e2 : 120 * (orderRatio : ℝ) * (K : ℝ) ^ 2 * (K : ℝ)⁻¹ = 120 * matrixOrder n := by
    rw [hh]; field_simp
  have e3 : (K : ℝ) * ((K : ℝ)⁻¹ * ∑ i, √(t i)) = ∑ i, √(t i) := by
    rw [← mul_assoc, hKinv, one_mul]
  linarith [e1, e2, e3, key]

end Zeta5Irr
