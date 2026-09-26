/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Tauext
public import Zeta5Irr.LocalFunctional.TauDeltaext
public import Zeta5Irr.LocalFunctional.TauFarMem
public import Zeta5Irr.LocalFunctional.Y

/-!
# The distributed functional `𝒯_p(A; R)`

Let `p` be a prime, `R ⊆ ℤ` finite and `A ∈ ℚ[x]`. For `0 ≤ a ≤ p - 1` split the poles `R`
according to their residue modulo `p`, rescaled by `r ↦ (r - a) / p`:
`R_a = {(r - a) / p : r ∈ R, r ≡ a (mod p)} ⊆ ℤ` are the poles that remain integral, and
`Σ_a = {(r - a) / p : r ∈ R, r ≢ a (mod p)} ⊆ ℚ_p` are the poles that move away, with
`v_p(s) = -1` for `s ∈ Σ_a`. The distributed functional is
`𝒯_p(A; R) = p^{-4} ∑_{a=0}^{p-1} τ_{Y_p}^ext(δ_{R_a}^ext(p^{-#R} A(a + pz) ∏_{s ∈ Σ_a} ε_s))`,
an element of `ℚ_p[X]`, where `ε_s` is the expansion of `1 / (z - s)` at the origin,
`δ^ext` the extended near-pole decomposition and `τ_{Y_p}^ext` the extended functional with
parameter `Y_p = p^5 X + C_p`.

## Main definitions

* `Zeta5Irr.distNearPoles p R a`: the set `R_a` of integral rescaled poles.
* `Zeta5Irr.distFarPoles p R a`: the set `Σ_a` of non-integral rescaled poles.
* `Zeta5Irr.tauDist p R A`: the distributed functional `𝒯_p(A; R) ∈ ℚ_p[X]`.

## Main results

* `Zeta5Irr.mem_distNearPoles`, `Zeta5Irr.mem_distFarPoles`: membership in `R_a` and `Σ_a`.
* `Zeta5Irr.mem_distNearPoles_iff_add_mul_mem`: `m ∈ R_a` iff `a + p m ∈ R`.
* `Zeta5Irr.norm_of_mem_distFarPoles`: `|s|_p = p`, i.e. `v_p(s) = -1`, for `s ∈ Σ_a`.
* `Zeta5Irr.prod_farEps_mem_tateAlgebra`: `∏_{s ∈ Σ_a} ε_s ∈ ℚ_p⟨z⟩`.
* `Zeta5Irr.tauDist_empty`: for `R = ∅` the pole sets are empty and
  `𝒯_p(A; ∅) = p^{-4} ∑_a τ_{Y_p}^ext(δ_∅^ext(A(a + pz)))`.

## Implementation notes

* `𝒯_p(-; R)` is a function `ℚ[x] → ℚ_p[X]` rather than a linear map. Its ingredients
  `δ^ext` and `τ^ext` take junk values on non-convergent input, so additivity is a theorem
  about convergent series, proved separately; it is not built into the definition.
* The sum over `0 ≤ a ≤ p - 1` is over `Finset.range p`. For `r ≡ a (mod p)` the rescaled pole
  `(r - a) / p` is computed by the exact integer division `Int.ediv`; for `r ≢ a (mod p)` it is
  the quotient `(r - a) / p` in `ℚ_p`.
* The substitution `A(a + pz)` is `A.comp (a + p X)` in `ℚ[X]`, mapped to `ℚ_p[z]` and then
  regarded as a power series; the scalars `p^{-#R}` and `p^{-4}` act by scalar multiplication.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.5 (Distribution).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial

variable (p : ℕ)

/-- The set `R_a = {(r - a) / p : r ∈ R, r ≡ a (mod p)} ⊆ ℤ` of poles of `R` congruent to `a`
modulo `p`, rescaled by `r ↦ (r - a) / p`. -/
@[zeta5irr "def_tau_dist"]
def distNearPoles (R : Finset ℤ) (a : ℕ) : Finset ℤ :=
  {r ∈ R | r ≡ a [ZMOD p]}.image fun r => (r - a) / p

/-- `m ∈ R_a` iff `m = (r - a) / p` for some `r ∈ R` with `r ≡ a (mod p)`. -/
theorem mem_distNearPoles {p : ℕ} {R : Finset ℤ} {a : ℕ} {m : ℤ} :
    m ∈ distNearPoles p R a ↔ ∃ r ∈ R, r ≡ a [ZMOD p] ∧ (r - a) / p = m := by
  simp [distNearPoles, and_assoc]

/-- For `R = ∅` there are no poles: `R_a = ∅` for every `a`. -/
@[simp]
theorem distNearPoles_empty (a : ℕ) : distNearPoles p ∅ a = ∅ := by
  simp [distNearPoles]

variable [Fact p.Prime]

open Classical in
/-- The set `Σ_a = {(r - a) / p : r ∈ R, r ≢ a (mod p)} ⊆ ℚ_p` of poles of `R` not congruent to
`a` modulo `p`, rescaled by `r ↦ (r - a) / p`. -/
@[zeta5irr "def_tau_dist"]
noncomputable def distFarPoles (R : Finset ℤ) (a : ℕ) : Finset ℚ_[p] :=
  {r ∈ R | ¬r ≡ a [ZMOD p]}.image fun r => ((r - a : ℤ) : ℚ_[p]) / p

/-- The distributed functional
`𝒯_p(A; R) = p^{-4} ∑_{a=0}^{p-1} τ_{Y_p}^ext(δ_{R_a}^ext(p^{-#R} A(a + pz) ∏_{s ∈ Σ_a} ε_s))`
in `ℚ_p[X]`. -/
@[zeta5irr "def_tau_dist"]
noncomputable def tauDist (R : Finset ℤ) (A : ℚ[X]) : ℚ_[p][X] :=
  ((p : ℚ_[p]) ^ 4)⁻¹ • ∑ a ∈ Finset.range p,
    tauExt (distNearPoles p R a) (Yp p) (deltaExt (distNearPoles p R a)
      (((p : ℚ_[p]) ^ R.card)⁻¹ •
        ((((A.comp (C (a : ℚ) + C (p : ℚ) * X)).map (algebraMap ℚ ℚ_[p]) : ℚ_[p][X]) :
          PowerSeries ℚ_[p]) * ∏ s ∈ distFarPoles p R a, farEps s)))

variable {p}

/-- `m ∈ R_a` iff `a + p m ∈ R`. -/
theorem mem_distNearPoles_iff_add_mul_mem {R : Finset ℤ} {a : ℕ} {m : ℤ} :
    m ∈ distNearPoles p R a ↔ (a : ℤ) + p * m ∈ R := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [mem_distNearPoles]
  constructor
  · rintro ⟨r, hr, hra, rfl⟩
    rwa [Int.mul_ediv_cancel' hra.symm.dvd, add_sub_cancel]
  · intro h
    refine ⟨_, h, (Int.modEq_iff_dvd.mpr ⟨m, by ring⟩).symm, ?_⟩
    rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hp]

/-- `s ∈ Σ_a` iff `s = (r - a) / p` for some `r ∈ R` with `r ≢ a (mod p)`. -/
theorem mem_distFarPoles {R : Finset ℤ} {a : ℕ} {s : ℚ_[p]} :
    s ∈ distFarPoles p R a ↔ ∃ r ∈ R, ¬r ≡ a [ZMOD p] ∧ ((r - a : ℤ) : ℚ_[p]) / p = s := by
  simp only [distFarPoles, Finset.mem_image, Finset.mem_filter, and_assoc]

/-- Every `s ∈ Σ_a` has `|s|_p = p`, that is `v_p(s) = -1 < 0`. -/
theorem norm_of_mem_distFarPoles {R : Finset ℤ} {a : ℕ} {s : ℚ_[p]}
    (hs : s ∈ distFarPoles p R a) : ‖s‖ = p := by
  obtain ⟨r, -, hra, rfl⟩ := mem_distFarPoles.mp hs
  exact norm_intCast_div_prime fun h => hra (Int.ModEq.symm (Int.modEq_iff_dvd.mpr h))

/-- The product `∏_{s ∈ Σ_a} ε_s` of far-pole series lies in `ℚ_p⟨z⟩`. -/
theorem prod_farEps_mem_tateAlgebra (R : Finset ℤ) (a : ℕ) :
    ∏ s ∈ distFarPoles p R a, farEps s ∈ tateAlgebra p :=
  Subalgebra.prod_mem _ fun s hs => farEps_mem_tateAlgebra (by
    rw [norm_inv, norm_of_mem_distFarPoles hs]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))

/-- For `R = ∅` there are no poles: `Σ_a = ∅` for every `a`. -/
@[simp]
theorem distFarPoles_empty (a : ℕ) : distFarPoles p ∅ a = ∅ := by
  simp [distFarPoles]

/-- The distributed functional without poles:
`𝒯_p(A; ∅) = p^{-4} ∑_{a=0}^{p-1} τ_{Y_p}^ext(δ_∅^ext(A(a + pz)))`. -/
theorem tauDist_empty (A : ℚ[X]) :
    tauDist p ∅ A = ((p : ℚ_[p]) ^ 4)⁻¹ • ∑ a ∈ Finset.range p,
      tauExt ∅ (Yp p) (deltaExt ∅
        ((((A.comp (C (a : ℚ) + C (p : ℚ) * X)).map (algebraMap ℚ ℚ_[p]) : ℚ_[p][X]) :
          PowerSeries ℚ_[p]))) := by
  simp only [tauDist, distFarPoles_empty, Finset.card_empty, pow_zero, inv_one, one_smul,
    Finset.prod_empty, mul_one]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [distNearPoles_empty]

end Zeta5Irr
