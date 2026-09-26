/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.Tauext
public import Zeta5Irr.LocalFunctional.LocalDeltaDiv

/-!
# Cancelling a linear factor against a pole in `τ_Y^ext ∘ δ^ext`

Let `R ⊆ ℤ` be finite, `r₀ ∈ R`, `Y ∈ ℚ_p[X]` and `f ∈ 𝒜 = ℚ_p⟨z⟩`. Then
`τ_Y^ext(δ_R^ext((z - r₀) f)) = τ_Y^ext(δ_{R \ {r₀}}^ext(f))`:
multiplying by `z - r₀` removes the pole at `r₀`.

Writing `R₁ = R \ {r₀}`, one first divides `f` by `E_{R₁}` in `𝒜`: `f = q E_{R₁} + b` with
`q ∈ 𝒜` and `deg b < #R₁`. Then `(z - r₀) f = q E_R + (z - r₀) b` is a division by
`E_R = (z - r₀) E_{R₁}`, so both near-pole decompositions have the Tate-algebra component `q`.
The residue of `(z - r₀) b / E_R` at `r₀` vanishes, and at `r ∈ R₁` it equals
`(r - r₀) b(r) / ((r - r₀) E_{R₁}'(r)) = b(r) / E_{R₁}'(r)`.

## Main results

* `Zeta5Irr.exists_eq_mul_intPoleProduct_add`: every `f ∈ ℚ_p⟨z⟩` is `q E_R + b` with
  `q ∈ ℚ_p⟨z⟩` and `deg b < #R`.
* `Zeta5Irr.tauExt_deltaExt_X_sub_C_mul`:
  `τ_Y^ext(δ_R^ext((z - r₀) f)) = τ_Y^ext(δ_{R \ {r₀}}^ext(f))`.

## Implementation notes

The division `f = q E_{R₁} + b` is obtained from the convergence of `δ_{R₁}(f^{[D]})`: its
Tate-algebra components `f^{[D]} /ₘ E_{R₁}` converge to some `q ∈ 𝒜`, and each coefficient of
degree `≥ #R₁` of `f - q E_{R₁}` is the limit of the corresponding coefficient of
`(f^{[D]} /ₘ E_{R₁} - q) E_{R₁}`, hence zero. The value of `E_R'` at `r ∈ R₁` is computed by
the product rule from `E_R = (z - r₀) E_{R₁}`, rather than from the product formula for the
derivative of `E_R` at a root.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- **Division by `E_R` in `ℚ_p⟨z⟩`.** For a finite set `R ⊆ ℤ` and `f ∈ ℚ_p⟨z⟩`, there are
`q ∈ ℚ_p⟨z⟩` and `b ∈ ℚ_p[z]` with `deg b < #R` and `f = q E_R + b`. -/
theorem exists_eq_mul_intPoleProduct_add (R : Finset ℤ) {f : ℚ_[p]⟦X⟧}
    (hf : f ∈ tateAlgebra p) :
    ∃ q : tateAlgebra p, ∃ b : Polynomial ℚ_[p], b.degree < R.card ∧
      f = (q : ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + b := by
  set E := intPoleProduct R ℚ_[p]
  set P : ℕ → Polynomial ℚ_[p] := fun D => trunc (D + 1) f /ₘ E
  set q : tateAlgebra p := (deltaExt R f).fst
  have hPq : Tendsto (fun D => tateAlgebra.ofPolynomial p (P D)) atTop (𝓝 q) := by
    have h := tendsto_deltaR_trunc_deltaExt (R := R) hf
    have hc : Continuous fun x : BT p R => x.fst := by fun_prop
    exact (hc.tendsto _).comp h
  have hPq' : Tendsto (fun D => ‖tateAlgebra.ofPolynomial p (P D) - q‖ *
      ‖tateAlgebra.ofPolynomial p E‖) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hPq).mul_const _
  set g : ℚ_[p]⟦X⟧ := f - (q : ℚ_[p]⟦X⟧) * (E : ℚ_[p]⟦X⟧)
  have hg : ∀ d, R.card ≤ d → coeff d g = 0 := by
    intro d hd
    refine norm_le_zero_iff.mp (ge_of_tendsto hPq' ?_)
    filter_upwards [eventually_ge_atTop d] with D hD
    have hmod : (trunc (D + 1) f %ₘ E).coeff d = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      refine (Polynomial.degree_modByMonic_lt _ (monic_intPoleProduct R ℚ_[p])).trans_le ?_
      rw [degree_intPoleProduct]
      exact_mod_cast hd
    have hcoeff : coeff d g =
        coeff d (((tateAlgebra.ofPolynomial p (P D) - q : tateAlgebra p) : ℚ_[p]⟦X⟧) *
          (E : ℚ_[p]⟦X⟧)) := by
      have h1 : coeff d f = (trunc (D + 1) f).coeff d := by
        rw [coeff_trunc, ite_eq_left (by omega)]
      have h2 : (trunc (D + 1) f).coeff d = (P D * E).coeff d := by
        conv_lhs => rw [← Polynomial.modByMonic_add_div (trunc (D + 1) f) E]
        rw [Polynomial.coeff_add, hmod, zero_add, mul_comm]
      rw [Subalgebra.coe_sub, tateAlgebra.coe_ofPolynomial, sub_mul, map_sub, ← Polynomial.coe_mul,
        map_sub, Polynomial.coeff_coe, ← h2, ← h1]
    rw [hcoeff]
    refine (le_tateNorm (mul_mem (Subtype.property _) (coe_mem_tateAlgebra E)) d).trans ?_
    exact tateNorm_mul_le (Subtype.property _) (coe_mem_tateAlgebra E)
  refine ⟨q, trunc R.card g, degree_trunc_lt _ _, ?_⟩
  have hgb : g = (trunc R.card g : ℚ_[p]⟦X⟧) := by
    ext d
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with h
    · rfl
    · exact hg d (by omega)
  rw [← hgb, add_sub_cancel]

/-- **Cancelling `z - r₀` against the pole at `r₀`.** Let `R ⊆ ℤ` be finite, `r₀ ∈ R`,
`Y ∈ ℚ_p[X]` and `f ∈ ℚ_p⟨z⟩`. Then
`τ_Y^ext(δ_R^ext((z - r₀) f)) = τ_Y^ext(δ_{R \ {r₀}}^ext(f))`. -/
@[zeta5irr "lem_local_tauext_cancel"]
theorem tauExt_deltaExt_X_sub_C_mul {R : Finset ℤ} {r₀ : ℤ} (hr₀ : r₀ ∈ R)
    (Y : Polynomial ℚ_[p]) {f : ℚ_[p]⟦X⟧} (hf : f ∈ tateAlgebra p) :
    tauExt R Y (deltaExt R ((X - C (r₀ : ℚ_[p])) * f)) =
      tauExt (R.erase r₀) Y (deltaExt (R.erase r₀) f) := by
  obtain ⟨q, b, hb, hfb⟩ := exists_eq_mul_intPoleProduct_add (R.erase r₀) hf
  set E₁ := intPoleProduct (R.erase r₀) ℚ_[p]
  set s : Polynomial ℚ_[p] := Polynomial.X - Polynomial.C (r₀ : ℚ_[p])
  have hE : intPoleProduct R ℚ_[p] = s * E₁ := by
    conv_lhs => rw [← Finset.insert_erase hr₀]
    exact intPoleProduct_insert _ (Finset.notMem_erase _ _)
  have hcard : (R.erase r₀).card + 1 = R.card := Finset.card_erase_add_one hr₀
  have hsb : (s * b).degree < R.card := by
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    rw [Polynomial.degree_mul, Polynomial.degree_X_sub_C, ← hcard,
      Polynomial.degree_eq_natDegree hb0]
    rw [Polynomial.degree_eq_natDegree hb0] at hb
    norm_cast at hb ⊢
    omega
  have hmul : (X - C (r₀ : ℚ_[p])) * f =
      (q : ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) +
        ((s * b : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
    rw [hfb, hE, Polynomial.coe_mul, Polynomial.coe_mul]
    simp only [s, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
    ring
  rw [deltaExt_eq_of_eq_mul_add hsb hmul, deltaExt_eq_of_eq_mul_add hb hfb, tauExt_mk,
    tauExt_mk]
  congr 1
  simp only [Finset.sum_coe_sort R (fun r : ℤ => ((s * b).eval (r : ℚ_[p]) /
      (Polynomial.derivative (intPoleProduct R ℚ_[p])).eval (r : ℚ_[p])) •
        (Polynomial.C ((harmonicFive (reflectIndex r) : ℚ) : ℚ_[p]) - Y)),
    Finset.sum_coe_sort (R.erase r₀) (fun r : ℤ => (b.eval (r : ℚ_[p]) /
      (Polynomial.derivative (intPoleProduct (R.erase r₀) ℚ_[p])).eval
        (r : ℚ_[p])) • (Polynomial.C ((harmonicFive (reflectIndex r) : ℚ) : ℚ_[p]) - Y))]
  rw [← Finset.add_sum_erase _ _ hr₀]
  simp only [s, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_self, zero_mul, zero_div, zero_smul, zero_add]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : (r : ℚ_[p]) - r₀ ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast Finset.ne_of_mem_erase hr)
  rw [hE, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_mul, eval_intPoleProduct_of_mem _ _ hr, mul_zero, zero_add]
  simp only [s, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_div_mul_left _ _ hr']
  rfl

end Zeta5Irr
