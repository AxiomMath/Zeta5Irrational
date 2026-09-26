/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.VpG
public import Zeta5Irr.LocalEstimates.InDetWeights
public import Zeta5Irr.LocalEstimates.DetAddRowSplit
public import Zeta5Irr.LocalEstimates.InWeightMax
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Gauss valuation of the determinant of a perturbed matrix

Let `A` be an `h × h` matrix over `ℚ_p[X]`, let `L` be an `h × h` matrix over `ℤ_p` of rank at
most `r₀` over `ℚ_p`, and let `w₁, …, w_h` be nonpositive half-integers with
`v_p^G(A_{rs}) ≥ w_r + w_s`. With `z₀ = #{r : w_r = 0}`,
`v_p^G(det(A + p⁻¹ L)) ≥ 2 ∑_r w_r - min(r₀, z₀)`.

Expanding `det(A + p⁻¹ L)` row by row gives a sum of determinants `det M_I`, where `M_I` takes
its rows in `I` from `p⁻¹ L` and its other rows from `A`. If `#I > r₀`, the rows of `L` in `I`
are linearly dependent over `ℚ_p`, hence so are the rows of `M_I` over `ℚ_p[X]`, and
`det M_I = 0`. If `#I ≤ r₀`, each term `± ∏_s (M_I)_{σ(s), s}` of the Leibniz expansion has
Gauss valuation at least `2 ∑_r w_r - (#I + ∑_{r ∈ I} w_r + ∑_{s ∈ σ⁻¹ I} w_s)`, and the
weight bound `card_add_two_mul_sum_le_min`, applied to `I` and to `σ⁻¹ I`, bounds the
correction by `min(r₀, z₀)`.

## Main results

* `Zeta5Irr.two_mul_sum_sub_min_le_vpG_det_add`: the bound
  `v_p^G(det(A + p⁻¹ L)) ≥ 2 ∑_r w_r - min(r₀, z₀)`.

## Implementation notes

* Half-integers are real numbers `w r` with `w r = n / 2` for some `n : ℤ`, as in
  `card_add_two_mul_sum_le_min`. Gauss valuations, which lie in `ℤ ∪ {+∞}`, are compared with
  real numbers after mapping `ℤ ∪ {+∞}` into `ℝ ∪ {+∞}` by `WithTop.map`.
* The matrix `p⁻¹ L` over `ℚ_p[X]` is the entrywise image `C (p⁻¹ * L_{rs})`, and the rank of
  `L` over `ℚ_p` is the rank of its entrywise image in `ℚ_p`.
* The proof works with the Gauss valuation attached to the pushforward of the `p`-adic
  valuation to `ℝ ∪ {+∞}`, so that the half-integer bounds are compared inside one ordered
  monoid.
* The source assumes `h ≥ 1`; the statement holds without it.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.7 (The outer range: the integral part and its
  correction).
-/

@[expose] public section

namespace Zeta5Irr

open Polynomial Finset

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- **Determinant of a perturbed matrix.** Let `A` be a square matrix over `ℚ_p[X]`, `L` a
square matrix over `ℤ_p` of rank at most `r₀` over `ℚ_p`, and `w` nonpositive half-integer
weights with `v_p^G(A_{rs}) ≥ w_r + w_s`. With `z₀ = #{r : w_r = 0}`,
`v_p^G(det(A + p⁻¹ L)) ≥ 2 ∑_r w_r - min(r₀, z₀)`. Gauss valuations are compared with reals
after mapping `ℤ ∪ {+∞}` into `ℝ ∪ {+∞}`. -/
@[zeta5irr "lem_det_perturb"]
theorem two_mul_sum_sub_min_le_vpG_det_add {h : ℕ} (A : Matrix (Fin h) (Fin h) ℚ_[p][X])
    (L : Matrix (Fin h) (Fin h) ℤ_[p]) (w : Fin h → ℝ) (hw_nonpos : ∀ r, w r ≤ 0)
    (hw_half : ∀ r, ∃ n : ℤ, w r = n / 2)
    (hA : ∀ r s, ((w r + w s : ℝ) : WithTop ℝ) ≤ (vpG (A r s)).map ((↑) : ℤ → ℝ))
    (r₀ : ℕ) (hL : (L.map ((↑) : ℤ_[p] → ℚ_[p])).rank ≤ r₀) :
    ((2 * ∑ r, w r - min (r₀ : ℝ) (#{r | w r = 0} : ℝ) : ℝ) : WithTop ℝ) ≤
      (vpG (A + L.map fun x => C ((p : ℚ_[p])⁻¹ * x)).det).map ((↑) : ℤ → ℝ) := by
  classical
  let g : WithTop ℤ →+o WithTop ℝ :=
    { (Int.castAddHom ℝ).withTopMap with monotone' := Int.cast_mono.withTop_map }
  set v := Padic.addValuation.map g rfl (R := ℚ_[p])
  have hV : ∀ B : ℚ_[p][X], (vpG B).map ((↑) : ℤ → ℝ) = gaussAddVal v B := fun B =>
    (gaussAddVal_map _ g rfl B).symm
  simp only [hV] at hA ⊢
  set LL := L.map ((↑) : ℤ_[p] → ℚ_[p])
  set m : ℝ := min (r₀ : ℝ) (#{r | w r = 0} : ℝ)
  -- Valuations of the entries of `p⁻¹ L`.
  have hv_coe : ∀ n : ℤ, g n = ((n : ℝ) : WithTop ℝ) := fun _ => rfl
  have hv_pinv : v ((p : ℚ_[p])⁻¹) = ((-1 : ℝ) : WithTop ℝ) := by
    change g (Padic.addValuation _) = _
    rw [Padic.addValuation.apply (by simp [(Fact.out : p.Prime).ne_zero]), hv_coe]
    simp
  have hv_L : ∀ x : ℤ_[p], (0 : WithTop ℝ) ≤ v x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    change (0 : WithTop ℝ) ≤ g (Padic.addValuation _)
    rw [Padic.addValuation.apply (show (x : ℚ_[p]) ≠ 0 by simpa using hx),
      PadicInt.valuation_coe, hv_coe]
    exact_mod_cast Nat.cast_nonneg _
  have hent : ∀ r s, ((-1 : ℝ) : WithTop ℝ) ≤ gaussAddVal v (C ((p : ℚ_[p])⁻¹ * L r s)) := by
    intro r s
    rw [gaussAddVal_C, v.map_mul, hv_pinv]
    simpa using add_le_add (le_refl (((-1 : ℝ) : WithTop ℝ))) (hv_L (L r s))
  rw [det_add_eq_sum_det_rowSplit]
  refine le_trans (Finset.le_inf fun I _ => ?_) (finset_inf_le_gaussAddVal_sum v _ _)
  set M : Matrix (Fin h) (Fin h) ℚ_[p][X] := Matrix.of fun r ↦
    if r ∈ I then (L.map fun x => C ((p : ℚ_[p])⁻¹ * x)) r else A r
  have hM : ∀ r s, M r s = if r ∈ I then C ((p : ℚ_[p])⁻¹ * L r s) else A r s := by
    intro r s
    simp only [M, Matrix.of_apply]
    split_ifs <;> rfl
  by_cases hI : r₀ < #I
  · -- Too many rows of `p⁻¹ L`: they are linearly dependent and the determinant vanishes.
    have hdep : ¬ LinearIndependent ℚ_[p] fun i : I => LL i := by
      intro hli
      have h1 := finrank_span_eq_card hli
      have h2 : Submodule.span ℚ_[p] (Set.range fun i : I => LL i) ≤
          Submodule.span ℚ_[p] (Set.range LL.row) :=
        Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
      have h3 := Submodule.finrank_mono h2
      rw [h1, ← Matrix.rank_eq_finrank_span_row, Fintype.card_coe] at h3
      omega
    obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
    set c' : Fin h → ℚ_[p] := fun r => if hr : r ∈ I then c ⟨r, hr⟩ else 0
    have hc'0 : ∀ r, r ∉ I → c' r = 0 := fun r hr => dite_eq_right_iff.mpr fun h => absurd h hr
    have hc' : ∑ r, c' r • LL r = 0 := by
      rw [← hc, ← Finset.sum_subset (subset_univ I) (fun r _ hr => by simp [hc'0 r hr]),
        ← Finset.sum_coe_sort I]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c', i.2]
    have hdet : M.det = 0 := by
      refine Matrix.det_eq_zero_of_not_linearIndependent_rows
        (Fintype.not_linearIndependent_iff.mpr ⟨fun r => C (c' r), ?_, i₀, ?_⟩)
      · ext s
        have hcs := congrFun hc' s
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcs ⊢
        have : ∀ r, C (c' r) * M r s = C ((p : ℚ_[p])⁻¹ * (c' r * LL r s)) := by
          intro r
          rw [hM]
          by_cases hr : r ∈ I
          · rw [ite_eq_left_iff.mpr (absurd hr), ← C_mul]
            congr 1
            change c' r * (_ * (L r s : ℚ_[p])) = _ * (c' r * (L r s : ℚ_[p]))
            ring
          · simp [hr, hc'0 r hr]
        simp_rw [this, ← map_sum, ← Finset.mul_sum, hcs, mul_zero, map_zero]
      · simpa [c', i₀.2] using hi₀
    rw [hdet, gaussAddVal_zero]
    exact le_top
  · push Not at hI
    refine le_gaussAddVal_det_of_forall_perm v M _ fun σ => ?_
    set β : Fin h → ℝ := fun s => if σ s ∈ I then -1 else w (σ s) + w s
    have hβ : ∀ s, ((β s : ℝ) : WithTop ℝ) ≤ gaussAddVal v (M (σ s) s) := by
      intro s
      rw [hM]
      by_cases hs : σ s ∈ I
      · simpa [β, hs] using hent (σ s) s
      · simpa [β, hs] using hA (σ s) s
    refine le_trans ?_ (Finset.sum_le_sum fun s _ => hβ s)
    rw [← WithTop.coe_sum, WithTop.coe_le_coe]
    set J := I.map σ.symm.toEmbedding
    have hJmem : ∀ s, s ∈ J ↔ σ s ∈ I := fun s => by simp [J, Finset.mem_map_equiv]
    have hJcard : #J = #I := card_map _
    have hJsum : ∑ s ∈ J, w (σ s) = ∑ r ∈ I, w r := by simp [J, Finset.sum_map]
    have hsplit : ∑ s, β s = ∑ s, (w (σ s) + w s) - ∑ s ∈ J, (1 + w (σ s) + w s) := by
      have hJ : ∑ s ∈ J, (1 + w (σ s) + w s) =
          ∑ s, if s ∈ J then 1 + w (σ s) + w s else 0 := by
        rw [Finset.sum_ite_mem, univ_inter]
      rw [eq_sub_iff_add_eq, hJ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : σ s ∈ I
      · simp only [β, hs, (hJmem s).mpr hs, ite_true]
        ring
      · simp [β, hs, (hJmem s).not.mpr hs]
    have hk : #I ≤ min r₀ h := le_min hI (by simpa using card_le_univ I)
    have hwI := card_add_two_mul_sum_le_min w hw_nonpos hw_half r₀ #I hk I rfl
    have hwJ := card_add_two_mul_sum_le_min w hw_nonpos hw_half r₀ #I hk J hJcard
    rw [hsplit, Finset.sum_add_distrib, Equiv.sum_comp σ w, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hJsum, Finset.sum_const, hJcard, nsmul_eq_mul, mul_one]
    simp only [m] at hwI hwJ ⊢
    linarith

end Padic

end Zeta5Irr
