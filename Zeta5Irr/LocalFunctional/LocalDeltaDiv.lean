/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.LocalDeltaConv
public import Zeta5Irr.LocalFunctional.TauTateMul

/-!
# `δ_R^ext` from a division by `E_R`

Let `R ⊆ ℤ` be finite, `E_R = ∏_{r ∈ R} (z - r)`, and let `f = q E_R + b` with `q ∈ 𝒜 = ℚ_p⟨z⟩`
and `b ∈ ℚ_p[z]` of degree `< #R`. Then
`δ_R^ext(f) = (q, (b(r) / E_R'(r))_{r ∈ R})`.

The truncations `q^{[D]}` of `q` converge to `q` in `𝒜`, so the polynomials
`V_D = q^{[D]} E_R + b` satisfy `‖f^{[D]} - V_D‖ ≤ ‖f^{[D]} - f‖ + ‖q^{[D]} - q‖ ‖E_R‖ → 0`
by the submultiplicativity of the Gauss norm. Since `δ_R` is linear and bounded,
`δ_R(f^{[D]}) - δ_R(V_D) → 0`. Finally `V_D = q^{[D]} E_R + b` is itself a Euclidean
division by `E_R`, and `V_D(r) = b(r)` for `r ∈ R`, so `δ_R(V_D) = (q^{[D]}, (b(r)/E_R'(r)))`,
which converges to `(q, (b(r)/E_R'(r)))`.

## Main results

* `Zeta5Irr.tendsto_ofPolynomial_trunc`: for `g ∈ 𝒜`, the truncations `g^{[D]}` converge to
  `g` in `𝒜`.
* `Zeta5Irr.deltaExt_eq_of_eq_mul_add`: if `f = q E_R + b` with `q ∈ 𝒜` and `deg b < #R`, then
  `δ_R^ext(f) = (q, (b(r) / E_R'(r))_{r ∈ R})`.

## Implementation notes

The source assumes `R` nonempty and `f ∈ 𝒜`. Neither is needed: `f ∈ 𝒜` follows from
`f = q E_R + b`, and the argument above does not use `R ≠ ∅`. The argument also avoids the
evaluation of power series at the points `r ∈ R` used in the source, comparing instead the
truncations of `f` with the polynomials `q^{[D]} E_R + b`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §4.4 (Completion at a prime).
-/

@[expose] public section

namespace Zeta5Irr

open Filter Topology PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- For `g ∈ ℚ_p⟨z⟩`, the truncations `g^{[D]} = ∑_{d ≤ D} g_d z^d` converge to `g` in
`ℚ_p⟨z⟩`. -/
theorem tendsto_ofPolynomial_trunc (g : tateAlgebra p) :
    Tendsto (fun D : ℕ => tateAlgebra.ofPolynomial p (trunc (D + 1) (g : ℚ_[p]⟦X⟧))) atTop
      (𝓝 g) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (mem_tateAlgebra_iff.mp g.2) (ε / 2) (half_pos hε)
  refine ⟨N, fun D hD => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), tateAlgebra.norm_def,
    Subalgebra.coe_sub, tateAlgebra.coe_ofPolynomial]
  refine (tateNorm_le_of_forall_norm_coeff_le fun d => ?_).trans_lt (half_lt_self hε)
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · simp [(half_pos hε).le]
  · have h' := hN d (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h'
    simpa using h'.le

/-- **`δ_R^ext` from a division by `E_R`.** Let `R ⊆ ℤ` be finite, `q ∈ ℚ_p⟨z⟩` and
`b ∈ ℚ_p[z]` with `deg b < #R`. If `f = q E_R + b`, then
`δ_R^ext(f) = (q, (b(r) / E_R'(r))_{r ∈ R})`. -/
@[zeta5irr "lem_local_delta_div"]
theorem deltaExt_eq_of_eq_mul_add {R : Finset ℤ} {f : ℚ_[p]⟦X⟧} {q : tateAlgebra p}
    {b : Polynomial ℚ_[p]} (hb : b.degree < R.card)
    (hf : f = (q : ℚ_[p]⟦X⟧) * (intPoleProduct R ℚ_[p] : ℚ_[p]⟦X⟧) + b) :
    deltaExt R f = BT.mk q fun r => b.eval ((r : ℤ) : ℚ_[p]) /
      (Polynomial.derivative (intPoleProduct R ℚ_[p])).eval ((r : ℤ) : ℚ_[p]) := by
  set E := intPoleProduct R ℚ_[p]
  set c : R → ℚ_[p] := fun r => b.eval ((r : ℤ) : ℚ_[p]) /
    (Polynomial.derivative E).eval ((r : ℤ) : ℚ_[p])
  set C := max 1 (⨆ r : R, ‖(Polynomial.derivative E).eval ((r : ℤ) : ℚ_[p])‖⁻¹)
  have hfA : f ∈ tateAlgebra p := by
    rw [hf]
    exact add_mem (mul_mem q.2 (coe_mem_tateAlgebra E)) (coe_mem_tateAlgebra b)
  set F : tateAlgebra p := ⟨f, hfA⟩
  set Q : ℕ → Polynomial ℚ_[p] := fun D => trunc (D + 1) (q : ℚ_[p]⟦X⟧)
  set Fp : ℕ → Polynomial ℚ_[p] := fun D => trunc (D + 1) f
  set V : ℕ → Polynomial ℚ_[p] := fun D => Q D * E + b
  have hFq : F = q * tateAlgebra.ofPolynomial p E + tateAlgebra.ofPolynomial p b :=
    Subtype.ext hf
  -- `δ_R(V_D) = (q^{[D]}, c)`
  have hV : ∀ D, deltaR R (V D) = BT.mk (tateAlgebra.ofPolynomial p (Q D)) c := by
    intro D
    rw [deltaR_eq_of_eq_mul_add (P := Q D) (B := b) rfl hb]
    congr 1
    funext r
    simp only [c, Polynomial.eval_add, Polynomial.eval_mul, E,
      eval_intPoleProduct_of_mem R ℚ_[p] r.2, mul_zero, zero_add]
  -- the error `f^{[D]} - V_D`
  have hdiff : ∀ D, tateAlgebra.ofPolynomial p (Fp D - V D) =
      (tateAlgebra.ofPolynomial p (Fp D) - F) -
        (tateAlgebra.ofPolynomial p (Q D) - q) * tateAlgebra.ofPolynomial p E := by
    intro D
    simp only [V, map_sub, map_add, map_mul, hFq]
    ring
  have hFt : Tendsto (fun D => ‖tateAlgebra.ofPolynomial p (Fp D) - F‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_ofPolynomial_trunc F)
  have hQt : Tendsto (fun D => ‖tateAlgebra.ofPolynomial p (Q D) - q‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_ofPolynomial_trunc q)
  have hmul : ∀ g h : tateAlgebra p, ‖g * h‖ ≤ ‖g‖ * ‖h‖ := fun g h =>
    tateNorm_mul_le g.2 h.2
  have herr : Tendsto (fun D => ‖tateAlgebra.ofPolynomial p (Fp D - V D)‖) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun D => ‖tateAlgebra.ofPolynomial p (Fp D) - F‖ +
        ‖tateAlgebra.ofPolynomial p (Q D) - q‖ * ‖tateAlgebra.ofPolynomial p E‖)
      (fun _ => norm_nonneg _) (fun D => ?_)
      (by simpa using hFt.add (hQt.mul_const ‖tateAlgebra.ofPolynomial p E‖))
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add_right (hmul _ _) _)
  refine deltaExt_eq_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.mpr ?_)
  refine squeeze_zero (g := fun D => C * ‖tateAlgebra.ofPolynomial p (Fp D - V D)‖ +
      ‖tateAlgebra.ofPolynomial p (Q D) - q‖)
    (fun _ => norm_nonneg _) (fun D => ?_) (by simpa using (herr.const_mul C).add hQt)
  have hmk : BT.mk (tateAlgebra.ofPolynomial p (Q D) - q) 0 =
      BT.mk (tateAlgebra.ofPolynomial p (Q D)) c - BT.mk q c := by
    rw [BT.mk, BT.mk, BT.mk, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
  have hsplit : deltaR R (Fp D) - BT.mk q c =
      deltaR R (Fp D - V D) + BT.mk (tateAlgebra.ofPolynomial p (Q D) - q) 0 := by
    rw [deltaR_sub, hV, hmk]
    abel
  change ‖deltaR R (Fp D) - BT.mk q c‖ ≤ _
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add (norm_deltaR_le _) ?_)
  rw [BT.norm_mk]
  simp

end Zeta5Irr
