/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Zeta5Irr.Attr
public import Zeta5Irr.LocalFunctional.IntPoleProduct
public import Zeta5Irr.LocalFunctional.TauTateMul
public import Zeta5Irr.LocalFunctional.LocalSeriesConv
public import Mathlib.Data.Finset.Slice
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Division by `E_R` of a `p`-adic series of integral polynomials

Let `p` be a prime, `R ⊆ ℤ` finite, and `U_ι ∈ ℤ_p[z]` for `ι ≥ 0`. The series
`∑_{ι ≥ 0} p^ι U_ι` converges in the Tate algebra `𝒜 = ℚ_p⟨z⟩`, and its sum `g` admits a
division with remainder by the pole polynomial `E_R = ∏_{r ∈ R} (z - r)`: there are `q ∈ 𝒜` and
`b ∈ ℚ_p[z]` with `deg b < #R` and `g = q E_R + b` in `𝒜`.

The proof divides each `U_ι` by the monic polynomial `E_R ∈ ℤ[z] ⊆ ℤ_p[z]`, giving
`U_ι = q_ι E_R + b_ι` with `q_ι, b_ι ∈ ℤ_p[z]` and `deg b_ι < #R`. Both series
`∑ p^ι q_ι` and `∑ p^ι b_ι` converge in `𝒜`; the coefficients of degree `≥ #R` of the second
sum vanish, so it is a polynomial of degree `< #R`, and passing to the limit in the partial
sums (using that multiplication by `E_R` is continuous on `𝒜`) gives the identity.

## Main results

* `Zeta5Irr.exists_eq_mul_intPoleProduct_add_of_tendsto`: the sum `g` of `∑ p^ι U_ι` in
  `ℚ_p⟨z⟩` is `q E_R + b` with `q ∈ ℚ_p⟨z⟩` and `deg b < #R`.

## Implementation notes

* The sum of the series is taken as a hypothesis: any `g ∈ ℚ_p⟨z⟩` with
  `‖∑_{ι < J} p^ι U_ι - g‖ → 0`; such a `g` exists by
  `Zeta5Irr.exists_tendsto_tateNorm_sum_pow_smul_sub` and is unique since the Gauss norm is a
  norm on `ℚ_p⟨z⟩`.
* The source assumes `R` nonempty and `r - r' ∈ ℤ_p^×` for distinct `r, r' ∈ R`, and obtains
  the integrality of `q_ι` through the bound `‖δ_R(U_ι)‖ ≤ ‖U_ι‖`. Neither hypothesis is
  needed: since `E_R` is monic with integer coefficients, Euclidean division of `U_ι` by `E_R`
  can be carried out in `ℤ_p[z]` itself. For `R = ∅` the conclusion reads `b = 0`, `q = g`.

## References

* Aabir Fauzan, *ζ(5) is irrational*, §5.5 (The inner range: the entry valuations).
-/

@[expose] public section

namespace Zeta5Irr

open PowerSeries Filter Topology Finset

variable {p : ℕ} [Fact p.Prime]

/-- **Division by `E_R` in `ℚ_p⟨z⟩`.** Let `R ⊆ ℤ` be finite and `U_ι ∈ ℤ_p[z]`, and let
`g ∈ ℚ_p⟨z⟩` be the sum of the series `∑_{ι ≥ 0} p^ι U_ι`. Then there are `q ∈ ℚ_p⟨z⟩` and
`b ∈ ℚ_p[z]` with `deg b < #R` and `g = q E_R + b`. -/
@[zeta5irr "lem_in_pdiv"]
theorem exists_eq_mul_intPoleProduct_add_of_tendsto (R : Finset ℤ) (U : ℕ → Polynomial ℤ_[p])
    {g : ℚ_[p]⟦X⟧} (hg : g ∈ tateAlgebra p)
    (hlim : Tendsto (fun J => tateNorm
      (∑ j ∈ range J, (p : ℚ_[p]) ^ j • (((U j).map PadicInt.Coe.ringHom : Polynomial ℚ_[p]) :
        ℚ_[p]⟦X⟧) - g)) atTop (𝓝 0)) :
    ∃ q ∈ tateAlgebra p, ∃ b : Polynomial ℚ_[p], b.degree < #R ∧
      g = q * ((intPoleProduct R ℚ_[p] : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) + (b : ℚ_[p]⟦X⟧) := by
  set ι : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  set E : Polynomial ℤ_[p] := intPoleProduct R ℤ_[p]
  have hE : E.Monic := monic_intPoleProduct R ℤ_[p]
  set Ê : ℚ_[p]⟦X⟧ := ((intPoleProduct R ℚ_[p] : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧)
  have hÊ : Ê = (((E.map ι) : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) := by
    rw [map_intPoleProduct]
  have hÊmem : Ê ∈ tateAlgebra p := coe_mem_tateAlgebra _
  -- the embedding `ℤ_p[z] → ℚ_p⟦z⟧`
  let emb : Polynomial ℤ_[p] → ℚ_[p]⟦X⟧ := fun V => ((V.map ι : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧)
  let S : (ℕ → Polynomial ℤ_[p]) → ℕ → ℚ_[p]⟦X⟧ := fun V J =>
    ∑ j ∈ range J, (p : ℚ_[p]) ^ j • emb (V j)
  have hSmem : ∀ V J, S V J ∈ tateAlgebra p := fun V J =>
    sum_mem fun j _ => Subalgebra.smul_mem _ (coe_mem_tateAlgebra _) _
  -- Euclidean division in `ℤ_p[z]`
  set qs : ℕ → Polynomial ℤ_[p] := fun j => U j /ₘ E
  set bs : ℕ → Polynomial ℤ_[p] := fun j => U j %ₘ E
  have hsplit : ∀ J, S U J = S qs J * Ê + S bs J := by
    intro J
    simp only [S, sum_mul, ← sum_add_distrib, smul_mul_assoc, ← smul_add]
    refine sum_congr rfl fun j _ => ?_
    congr 1
    simp only [emb, hÊ, qs, bs, ← Polynomial.coe_mul, ← Polynomial.coe_add,
      ← Polynomial.map_mul, ← Polynomial.map_add]
    rw [add_comm, mul_comm, Polynomial.modByMonic_add_div]
  obtain ⟨q, hq, hqlim⟩ := exists_tendsto_tateNorm_sum_pow_smul_sub qs
  obtain ⟨b', hb', hblim⟩ := exists_tendsto_tateNorm_sum_pow_smul_sub bs
  change Tendsto (fun J => tateNorm (S qs J - q)) atTop (𝓝 0) at hqlim
  change Tendsto (fun J => tateNorm (S bs J - b')) atTop (𝓝 0) at hblim
  change Tendsto (fun J => tateNorm (S U J - g)) atTop (𝓝 0) at hlim
  -- the high coefficients of `b'` vanish
  have hdeg : ∀ j, (bs j).natDegree < #R ∨ bs j = 0 := by
    intro j
    by_cases h0 : bs j = 0
    · exact Or.inr h0
    left
    have hlt := Polynomial.degree_modByMonic_lt (U j) hE
    rw [← natDegree_intPoleProduct R ℤ_[p]]
    exact (Polynomial.natDegree_lt_natDegree h0 hlt)
  have hcoeff : ∀ k, #R ≤ k → coeff k b' = 0 := by
    intro k hk
    have hSk : ∀ J, coeff k (S bs J) = 0 := by
      intro J
      simp only [S, emb, map_sum, map_smul, Polynomial.coeff_coe, Polynomial.coeff_map]
      refine sum_eq_zero fun j _ => ?_
      rcases hdeg j with h | h
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (h.trans_le hk), map_zero, smul_zero]
      · simp [h]
    have hle : ∀ J, ‖coeff k b'‖ ≤ tateNorm (S bs J - b') := by
      intro J
      have := le_tateNorm (sub_mem (hSmem bs J) hb') k
      simpa [hSk J] using this
    have : ‖coeff k b'‖ ≤ 0 := ge_of_tendsto' hblim hle
    exact norm_le_zero_iff.mp this
  refine ⟨q, hq, trunc #R b', degree_trunc_lt b' _, ?_⟩
  have htrunc : ((trunc #R b' : Polynomial ℚ_[p]) : ℚ_[p]⟦X⟧) = b' := by
    ext k
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with h
    · rfl
    · exact (hcoeff k (not_lt.mp h)).symm
  rw [htrunc]
  -- uniqueness of the limit
  set D := g - (q * Ê + b')
  have hD : D ∈ tateAlgebra p :=
    sub_mem hg (add_mem (mul_mem_tateAlgebra hq hÊmem) hb')
  have hbound : ∀ J, tateNorm D ≤
      max (max (tateNorm (S qs J - q) * tateNorm Ê) (tateNorm (S bs J - b')))
        (tateNorm (S U J - g)) := by
    intro J
    have hDeq : D = ((S qs J - q) * Ê + (S bs J - b')) + -(S U J - g) := by
      simp only [D, hsplit J]; ring
    have h1 : S qs J - q ∈ tateAlgebra p := sub_mem (hSmem qs J) hq
    have h2 : S bs J - b' ∈ tateAlgebra p := sub_mem (hSmem bs J) hb'
    have h3 : S U J - g ∈ tateAlgebra p := sub_mem (hSmem U J) hg
    rw [hDeq]
    refine (tateNorm_add_le_max (add_mem (mul_mem_tateAlgebra h1 hÊmem) h2)
      (neg_mem h3)).trans ?_
    rw [tateNorm_neg]
    refine max_le_max ?_ le_rfl
    exact (tateNorm_add_le_max (mul_mem_tateAlgebra h1 hÊmem) h2).trans
      (max_le_max (tateNorm_mul_le h1 hÊmem) le_rfl)
  have hlim0 : Tendsto (fun J => max (max (tateNorm (S qs J - q) * tateNorm Ê)
      (tateNorm (S bs J - b'))) (tateNorm (S U J - g))) atTop (𝓝 0) := by
    have := ((hqlim.mul_const (tateNorm Ê)).max hblim).max hlim
    simpa using this
  have hD0 : tateNorm D ≤ 0 := ge_of_tendsto' hlim0 hbound
  have : D = 0 := (tateNorm_eq_zero_iff hD).mp (le_antisymm hD0 (tateNorm_nonneg _))
  exact (sub_eq_zero.mp this)

end Zeta5Irr
