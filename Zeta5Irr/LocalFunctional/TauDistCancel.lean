/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.TauDist
public import Zeta5Irr.LocalFunctional.LocalTauextCancel
public import Zeta5Irr.LocalFunctional.TauFarMem

/-!
# Cancelling a linear factor against a pole in `𝒯_p(A; R)`

Let `p` be a prime, `R ⊆ ℤ` finite, `r₀ ∈ R` and `A ∈ ℚ[x]` divisible by `x - r₀`. Then
`𝒯_p(A; R) = 𝒯_p(A / (x - r₀); R \ {r₀})`.

Write `A = (x - r₀) A₁` and `ρ₀ = (r₀ - a) / p`, so that `A(a + pz) = p (z - ρ₀) A₁(a + pz)`,
and the factor `p` turns `p^{-#R}` into `p^{-#(R \ {r₀})}`. We compare the `a`-th summands of
the two sides. If `r₀ ≡ a (mod p)`, then `ρ₀ ∈ ℤ` is a near pole, `R_a = R'_a ∪ {ρ₀}` and
`Σ_a = Σ'_a`, and the factor `z - ρ₀` cancels against the pole `ρ₀` in `τ_Y^ext ∘ δ^ext`.
If `r₀ ≢ a (mod p)`, then `ρ₀` is a far pole, `R_a = R'_a`, `Σ_a = Σ'_a ∪ {ρ₀}`, and
`(z - ρ₀) ε_{ρ₀} = 1`.

## Main results

* `Zeta5Irr.map_X_sub_C_comp_add_mul`: `(x - r₀)(a + pz) = p (z - (r₀ - a) / p)`.
* `Zeta5Irr.tauDist_X_sub_C_mul`: `𝒯_p((x - r₀) A₁; R) = 𝒯_p(A₁; R \ {r₀})`.
* `Zeta5Irr.tauDist_eq_tauDist_erase_divByMonic`: for `x - r₀ ∣ A`,
  `𝒯_p(A; R) = 𝒯_p(A / (x - r₀); R \ {r₀})`.

## Implementation notes

The quotient `A / (x - r₀)` is the division `A /ₘ (x - r₀)` by the monic polynomial `x - r₀`,
which is exact under the divisibility hypothesis.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The substituted linear factor: `(x - r₀)(a + pz) = p (z - (r₀ - a) / p)` in `ℚ_p[z]`. -/
theorem map_X_sub_C_comp_add_mul (r₀ : ℤ) (a : ℕ) :
    ((X - C (r₀ : ℚ)).comp (C (a : ℚ) + C (p : ℚ) * X)).map (algebraMap ℚ ℚ_[p]) =
      C (p : ℚ_[p]) * (X - C (((r₀ - a : ℤ) : ℚ_[p]) / p)) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [sub_comp, X_comp, C_comp, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, map_C, map_X, mul_sub, ← C_mul, mul_div_cancel₀ _ hp]
  simp only [eq_ratCast, Rat.cast_intCast, Rat.cast_natCast, Int.cast_sub, Int.cast_natCast,
    C_sub]
  ring

/-- If `a + p m = r₀`, then removing `r₀` from `R` removes `m` from `R_a`. -/
theorem distNearPoles_erase_of_add_mul_eq {R : Finset ℤ} {r₀ m : ℤ} {a : ℕ}
    (hma : (a : ℤ) + p * m = r₀) :
    distNearPoles p (R.erase r₀) a = (distNearPoles p R a).erase m := by
  ext n
  rw [Finset.mem_erase, mem_distNearPoles_iff_add_mul_mem, mem_distNearPoles_iff_add_mul_mem,
    Finset.mem_erase, ← hma]
  simp [(Fact.out : p.Prime).ne_zero]

/-- If `r₀ ≡ a (mod p)`, then removing `r₀` from `R` leaves `Σ_a` unchanged. -/
theorem distFarPoles_erase_of_modEq {R : Finset ℤ} {r₀ : ℤ} {a : ℕ} (h : r₀ ≡ a [ZMOD p]) :
    distFarPoles p (R.erase r₀) a = distFarPoles p R a := by
  ext s
  simp only [mem_distFarPoles, Finset.mem_erase]
  grind

/-- If `r₀ ≢ a (mod p)`, then removing `r₀` from `R` leaves `R_a` unchanged. -/
theorem distNearPoles_erase_of_not_modEq {R : Finset ℤ} {r₀ : ℤ} {a : ℕ}
    (h : ¬r₀ ≡ a [ZMOD p]) : distNearPoles p (R.erase r₀) a = distNearPoles p R a := by
  ext n
  rw [mem_distNearPoles_iff_add_mul_mem, mem_distNearPoles_iff_add_mul_mem, Finset.mem_erase]
  exact ⟨And.right, fun hn => ⟨fun hn' => h (Int.modEq_iff_dvd.mpr ⟨n, by rw [← hn']; ring⟩).symm,
    hn⟩⟩

/-- The rescaled pole `(r₀ - a) / p` is not in `Σ_a` for `R \ {r₀}`. -/
theorem div_notMem_distFarPoles_erase (R : Finset ℤ) (r₀ : ℤ) (a : ℕ) :
    ((r₀ - a : ℤ) : ℚ_[p]) / p ∉ distFarPoles p (R.erase r₀) a := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [mem_distFarPoles]
  rintro ⟨r, hr, -, hrρ⟩
  rw [div_left_inj' hp, Int.cast_inj, sub_left_inj] at hrρ
  exact Finset.notMem_erase r₀ R (hrρ ▸ hr)

/-- If `r₀ ∈ R` and `r₀ ≢ a (mod p)`, then `Σ_a = Σ'_a ∪ {(r₀ - a) / p}`, where `Σ'_a` is
`Σ_a` for `R \ {r₀}`. -/
theorem distFarPoles_eq_insert_erase [DecidableEq ℚ_[p]] {R : Finset ℤ} {r₀ : ℤ} {a : ℕ}
    (hr₀ : r₀ ∈ R) (h : ¬r₀ ≡ a [ZMOD p]) :
    distFarPoles p R a =
      insert (((r₀ - a : ℤ) : ℚ_[p]) / p) (distFarPoles p (R.erase r₀) a) := by
  ext s
  simp only [Finset.mem_insert, mem_distFarPoles, Finset.mem_erase]
  grind

/-- **Cancelling `x - r₀` in `𝒯_p`.** For a prime `p`, a finite `R ⊆ ℤ`, `r₀ ∈ R` and
`A₁ ∈ ℚ[x]`, `𝒯_p((x - r₀) A₁; R) = 𝒯_p(A₁; R \ {r₀})`. -/
theorem tauDist_X_sub_C_mul {R : Finset ℤ} {r₀ : ℤ} (hr₀ : r₀ ∈ R) (A : ℚ[X]) :
    tauDist p R ((X - C (r₀ : ℚ)) * A) = tauDist p (R.erase r₀) A := by
  classical
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : ((p : ℚ_[p]) ^ (R.erase r₀).card)⁻¹ = ((p : ℚ_[p]) ^ R.card)⁻¹ * p := by
    rw [← Finset.card_erase_add_one hr₀, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hp,
      mul_one]
  unfold tauDist
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  set ρ : ℚ_[p] := ((r₀ - a : ℤ) : ℚ_[p]) / p with hρ
  set B : PowerSeries ℚ_[p] :=
    (((A.comp (C (a : ℚ) + C (p : ℚ) * X)).map (algebraMap ℚ ℚ_[p]) : ℚ_[p][X]) :
      PowerSeries ℚ_[p]) with hB
  have hcomp : (((((X - C (r₀ : ℚ)) * A).comp (C (a : ℚ) + C (p : ℚ) * X)).map
      (algebraMap ℚ ℚ_[p]) : ℚ_[p][X]) : PowerSeries ℚ_[p]) =
      PowerSeries.C (p : ℚ_[p]) * ((PowerSeries.X - PowerSeries.C ρ) * B) := by
    rw [mul_comp, Polynomial.map_mul, map_X_sub_C_comp_add_mul, coe_mul, coe_mul, coe_C,
      coe_sub, coe_X, coe_C, mul_assoc]
  by_cases h : r₀ ≡ a [ZMOD p]
  · obtain ⟨m, hm⟩ := h.symm.dvd
    have hma : (a : ℤ) + p * m = r₀ := by rw [← hm, add_sub_cancel]
    have hmρ : ((m : ℤ) : ℚ_[p]) = ρ := by
      rw [hρ, eq_div_iff hp, hm]
      push_cast
      ring
    rw [distNearPoles_erase_of_add_mul_eq hma, distFarPoles_erase_of_modEq h,
      ← tauExt_deltaExt_X_sub_C_mul (mem_distNearPoles_iff_add_mul_mem.mpr (hma ▸ hr₀)) _
        (Subalgebra.smul_mem _
          (Subalgebra.mul_mem _ (coe_mem_tateAlgebra _) (prod_farEps_mem_tateAlgebra R a)) _),
      hmρ, hcomp, hcard]
    congr 2
    simp only [PowerSeries.smul_eq_C_mul, map_mul]
    ring
  · have hfar := distFarPoles_eq_insert_erase (p := p) hr₀ h
    have hρ0 : ρ ≠ 0 := by
      intro h0
      have := norm_of_mem_distFarPoles (hfar ▸ Finset.mem_insert_self ρ _)
      rw [h0, norm_zero] at this
      exact hp (by exact_mod_cast this.symm)
    rw [distNearPoles_erase_of_not_modEq h, hfar,
      Finset.prod_insert (div_notMem_distFarPoles_erase (p := p) R r₀ a), hcomp, hcard]
    congr 2
    simp only [PowerSeries.smul_eq_C_mul, map_mul]
    linear_combination (PowerSeries.C ((p : ℚ_[p]) ^ R.card)⁻¹ * PowerSeries.C (p : ℚ_[p]) * B *
      ∏ s ∈ distFarPoles p (R.erase r₀) a, farEps s) * X_sub_C_mul_farEps hρ0

/-- **Cancelling a pole in `𝒯_p`.** For a prime `p`, a finite `R ⊆ ℤ`, `r₀ ∈ R` and
`A ∈ ℚ[x]` divisible by `x - r₀`, `𝒯_p(A; R) = 𝒯_p(A / (x - r₀); R \ {r₀})`. -/
@[zeta5irr "lem_tau_dist_cancel"]
theorem tauDist_eq_tauDist_erase_divByMonic {R : Finset ℤ} {r₀ : ℤ} (hr₀ : r₀ ∈ R) {A : ℚ[X]}
    (hA : X - C (r₀ : ℚ) ∣ A) :
    tauDist p R A = tauDist p (R.erase r₀) (A /ₘ (X - C (r₀ : ℚ))) := by
  obtain ⟨A₁, rfl⟩ := hA
  rw [mul_divByMonic_cancel_left _ (monic_X_sub_C _), tauDist_X_sub_C_mul hr₀]

end Zeta5Irr
